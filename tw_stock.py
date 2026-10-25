# -*- coding: utf-8 -*-
"""
台股每日分析儀表板
------------------
執行:  python tw_stock.py
會自動:
  1. 從證交所 / 櫃買中心下載近 65 個交易日的全市場行情與三大法人資料(第一次約 3 分鐘，之後每天只抓新資料)
  2. 計算技術指標，篩選「今日推薦股」與「潛力股」，並給出建議進場區間 / 停損 / 目標價
  3. 開啟瀏覽器顯示儀表板；盤中(09:00~13:30)每 15 秒更新即時報價

只用 Python 標準函式庫，不需安裝任何套件 (Python 3.8 以上)。
本程式僅為技術分析輔助工具，不構成投資建議。
"""
import gzip
import json
import math
import os
import re
import ssl
import sys
import threading
import time
import traceback
import urllib.parse
import urllib.request
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

PORT = 8765
HISTORY_DAYS = 65          # 需要的交易日數 (MA60 需要 60 天)
INST_DAYS = 10             # 法人資料天數
MAX_LOOKBACK = 140         # 最多往回找幾個日曆天
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "tw_stock_data")
os.makedirs(DATA_DIR, exist_ok=True)

UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36"

# 證交所憑證在 Python 3.13 的嚴格驗證下會失敗，放寬這個旗標(仍會驗證憑證)
SSL_CTX = ssl.create_default_context()
if hasattr(ssl, "VERIFY_X509_STRICT"):
    SSL_CTX.verify_flags &= ~ssl.VERIFY_X509_STRICT

# 每個主機的最小請求間隔(秒)，避免被證交所封鎖 IP
_RATE = {"www.twse.com.tw": 2.0, "www.tpex.org.tw": 0.6}
_last_req = {}
_rate_lock = threading.Lock()

STATUS = {"state": "starting", "msg": "啟動中…", "progress": 0, "report_time": None}
REPORT = {}
HIST = {}      # code -> dict(market,name,dates,o,h,l,c,v)
INST = {}      # code -> list of (date, foreign, trust, dealer) 單位: 張
FUND = {}      # code -> (pe, yield, pb)


def log(msg):
    STATUS["msg"] = msg
    print(datetime.now().strftime("%H:%M:%S"), msg, flush=True)


def http_get(url, timeout=30, retries=3):
    host = urllib.parse.urlparse(url).netloc
    for attempt in range(retries):
        gap = _RATE.get(host, 0)
        if gap:
            with _rate_lock:
                wait = _last_req.get(host, 0) + gap - time.time()
                _last_req[host] = time.time() + max(wait, 0)
            if wait > 0:
                time.sleep(wait)
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as r:
                raw = r.read()
                if r.headers.get("Content-Encoding") == "gzip":
                    raw = gzip.decompress(raw)
                return json.loads(raw.decode("utf-8", "replace"))
        except Exception as e:
            if attempt == retries - 1:
                raise
            time.sleep(3 * (attempt + 1))


def num(s):
    """把 '1,234.5' / '--' / '' 轉成 float 或 None"""
    if s is None:
        return None
    if isinstance(s, (int, float)):
        return float(s)
    s = str(s).replace(",", "").replace("+", "").strip()
    if s in ("", "--", "---", "-", "X", "除權", "除息"):
        return None
    try:
        return float(s)
    except ValueError:
        return None


# ---------------------------------------------------------------- 資料抓取 / 快取
def cache_path(kind, d):
    return os.path.join(DATA_DIR, f"{d:%Y%m%d}_{kind}.json")


def load_cache(kind, d):
    p = cache_path(kind, d)
    if os.path.exists(p):
        try:
            with open(p, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return None
    return None


def save_cache(kind, d, obj):
    with open(cache_path(kind, d), "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, separators=(",", ":"))


def is_etf(code):
    # ETF: 00 開頭，例如 0050、00878、00631L、006201
    return code.startswith("00") and 4 <= len(code) <= 6 and code[:4].isdigit() and code.isalnum()


def sec_type(code):
    """證券種類：股票 / ETF / 特別股 / ETN / REIT / TDR（權證、牛熊證不收）"""
    import re
    if is_etf(code):
        return "ETF"
    if re.fullmatch(r"\d{4}", code):
        return "股票"
    if re.fullmatch(r"\d{4}[A-Z]\d?", code):
        return "特別股"
    if re.fullmatch(r"02\d{4}", code):
        return "ETN"
    if re.fullmatch(r"01\d{3}T", code):
        return "REIT"
    if re.fullmatch(r"91\d{4}", code):
        return "TDR"
    return None


def is_nonstock(code):
    return sec_type(code) not in ("股票", None)


def is_stock_code(code):
    return sec_type(code) is not None


def fetch_twse_quotes(d):
    """回傳 {'holiday':True} 或 {'stocks':{code:[name,o,h,l,c,vol張]}, 'index':[close,chg_pct]}"""
    url = f"https://www.twse.com.tw/rwd/zh/afterTrading/MI_INDEX?date={d:%Y%m%d}&type=ALLBUT0999&response=json"
    js = http_get(url)
    if js.get("stat") != "OK":
        return {"holiday": True}
    out, idx = {}, None
    for t in js.get("tables", []):
        fields = t.get("fields") or []
        if "證券代號" in fields and "收盤價" in fields:
            fi = {f: i for i, f in enumerate(fields)}
            for row in t["data"]:
                code = row[fi["證券代號"]].strip()
                if not is_stock_code(code):
                    continue
                c = num(row[fi["收盤價"]])
                vol = num(row[fi["成交股數"]]) or 0
                out[code] = [row[fi["證券名稱"]].strip(), num(row[fi["開盤價"]]), num(row[fi["最高價"]]),
                             num(row[fi["最低價"]]), c, round(vol / 1000)]
        elif "收盤指數" in fields and idx is None:
            for row in t["data"]:
                if row[0].strip() == "發行量加權股價指數":
                    idx = [num(row[1]), num(row[4]) or 0]
    if not out:
        return {"holiday": True}
    return {"stocks": out, "index": idx}


def fetch_tpex_quotes(d):
    url = f"https://www.tpex.org.tw/www/zh-tw/afterTrading/dailyQuotes?date={d:%Y}%2F{d:%m}%2F{d:%d}&response=json"
    js = http_get(url)
    out = {}
    for t in js.get("tables", []):
        fields = t.get("fields") or []
        if "代號" not in fields or "收盤" not in fields:
            continue
        fi = {f.strip(): i for i, f in enumerate(fields)}
        for row in t.get("data", []):
            code = row[fi["代號"]].strip()
            if not is_stock_code(code):
                continue
            vol = num(row[fi["成交股數"]]) or 0
            out[code] = [row[fi["名稱"]].strip(), num(row[fi["開盤"]]), num(row[fi["最高"]]),
                         num(row[fi["最低"]]), num(row[fi["收盤"]]), round(vol / 1000)]
    if not out:
        return {"holiday": True}
    return {"stocks": out}


def fetch_twse_inst(d):
    url = f"https://www.twse.com.tw/rwd/zh/fund/T86?date={d:%Y%m%d}&selectType=ALLBUT0999&response=json"
    js = http_get(url)
    if js.get("stat") != "OK":
        return {"holiday": True}
    out = {}
    for row in js.get("data", []):
        code = row[0].strip()
        if is_stock_code(code):
            # 外資(不含自營)、投信、自營商合計  -> 張
            out[code] = [round((num(row[4]) or 0) / 1000), round((num(row[10]) or 0) / 1000),
                         round((num(row[11]) or 0) / 1000)]
    return {"inst": out} if out else {"holiday": True}


def fetch_tpex_inst(d):
    url = (f"https://www.tpex.org.tw/www/zh-tw/insti/dailyTrade?type=Daily&sect=EW"
           f"&date={d:%Y}%2F{d:%m}%2F{d:%d}&response=json")
    js = http_get(url)
    out = {}
    for t in js.get("tables", []):
        for row in t.get("data", []):
            code = row[0].strip()
            if is_stock_code(code) and len(row) >= 24:
                out[code] = [round((num(row[10]) or 0) / 1000), round((num(row[13]) or 0) / 1000),
                             round((num(row[22]) or 0) / 1000)]
    return {"inst": out} if out else {"holiday": True}


def candidate_dates():
    """由今天往回列出平日(週一~週五)。收盤資料約 14:30 後才有，所以 14:40 前不抓今天"""
    now = datetime.now()
    d = now.date()
    if now.hour * 60 + now.minute < 14 * 60 + 40:
        d -= timedelta(days=1)
    out = []
    for i in range(MAX_LOOKBACK):
        x = d - timedelta(days=i)
        if x.weekday() < 5:
            out.append(x)
    return out


def get_day(kind, fetcher, d):
    """從快取讀取，沒有就下載。休市日只在確定已過去時才快取"""
    c = load_cache(kind, d)
    if c is not None:
        return c
    try:
        res = fetcher(d)
    except Exception as e:
        print(f"  ! 下載 {kind} {d} 失敗: {e}")
        return None
    today = date.today()
    if not res.get("holiday") or d < today - timedelta(days=1):
        save_cache(kind, d, res)
    return res


def update_data():
    global HIST, INST, FUND
    STATUS.update(state="loading", progress=0)
    dates = candidate_dates()
    trading = []   # (date, twse, tpex_future)
    pool = ThreadPoolExecutor(max_workers=3)   # 櫃買資料較大，和證交所平行下載
    log("下載歷史行情中(第一次執行約需 3~5 分鐘，之後會使用快取)…")
    for d in dates:
        if len(trading) >= HISTORY_DAYS:
            break
        tw = get_day("twse3", fetch_twse_quotes, d)
        if tw is None:   # 多半是請求太頻繁被暫時擋下，稍等再試一次
            time.sleep(15)
            tw = get_day("twse3", fetch_twse_quotes, d)
        if tw is None or tw.get("holiday"):
            continue
        trading.append((d, tw, pool.submit(get_day, "tpex3", fetch_tpex_quotes, d)))
        STATUS["progress"] = int(len(trading) / HISTORY_DAYS * 75)
        STATUS["msg"] = f"行情資料 {len(trading)}/{HISTORY_DAYS} 天 (目前: {d:%Y-%m-%d})"
    STATUS["msg"] = "等待上櫃行情下載完成…"
    trading = [(d, tw, fut.result() or {}) for d, tw, fut in trading]
    STATUS["progress"] = 80
    if not trading:
        raise RuntimeError("無法取得任何行情資料，請確認網路連線")
    trading.reverse()  # 舊 -> 新

    # 建立每檔股票的歷史序列
    hist = {}
    taiex = []
    for d, tw, tp in trading:
        ds = d.strftime("%Y-%m-%d")
        if tw.get("index"):
            close = tw["index"][0]
            pct = round((close / taiex[-1][1] - 1) * 100, 2) if taiex else tw["index"][1]
            taiex.append((ds, close, pct))
        for market, src in (("上市", tw.get("stocks", {})), ("上櫃", tp.get("stocks", {}))):
            for code, (name, o, h, l, c, v) in src.items():
                if c is None:
                    continue
                s = hist.setdefault(code, {"market": market, "name": name, "dates": [], "o": [], "h": [],
                                           "l": [], "c": [], "v": []})
                s["name"] = name
                s["dates"].append(ds)
                s["o"].append(o or c); s["h"].append(h or c); s["l"].append(l or c)
                s["c"].append(c); s["v"].append(v)

    # 法人
    log("下載三大法人買賣超…")
    inst = {}
    days = [d for d, _, _ in trading[-INST_DAYS:]]
    futs = [(d, pool.submit(get_day, "tpinst3", fetch_tpex_inst, d)) for d in days]
    tw_inst = []
    for i, d in enumerate(days):
        tw_inst.append((d, get_day("twinst3", fetch_twse_inst, d)))
        STATUS["progress"] = 80 + int((i + 1) / len(days) * 15)
    for d, r in tw_inst + [(d, f.result()) for d, f in futs]:
        if r and r.get("inst"):
            for code, vals in r["inst"].items():
                inst.setdefault(code, []).append([d.strftime("%Y-%m-%d")] + vals)
    for v in inst.values():
        v.sort(key=lambda x: x[0])
    pool.shutdown()

    # 本益比 / 殖利率 (只取最新)
    log("下載本益比 / 殖利率…")
    fund = {}
    try:
        for r in http_get("https://openapi.twse.com.tw/v1/exchangeReport/BWIBBU_ALL"):
            fund[r["Code"]] = (num(r.get("PEratio")), num(r.get("DividendYield")), num(r.get("PBratio")))
    except Exception as e:
        print("  ! 上市本益比下載失敗", e)
    try:
        for r in http_get("https://www.tpex.org.tw/openapi/v1/tpex_mainboard_peratio_analysis"):
            fund[r["SecuritiesCompanyCode"]] = (num(r.get("PriceEarningRatio")), num(r.get("YieldRatio")),
                                                num(r.get("PriceBookRatio")))
    except Exception as e:
        print("  ! 上櫃本益比下載失敗", e)

    HIST, INST, FUND = hist, inst, fund
    global PROFILE, IND_PE
    log("下載公司基本資料、EPS、營收、股利…")
    PROFILE = load_profiles()
    IND_PE = compute_ind_pe()
    global RISK, HIST2
    log("下載籌碼結構與注意/處置股資料…")
    RISK = load_risk(trading[-1][0])
    global DTLIST, DIVH
    DTLIST = load_dtlist(trading[-1][0])
    DIVH = load_divhist(trading[-1][0])
    global NOLIM
    NOLIM = load_nolimit(trading[-1][0])
    global EXTRA, TAIEX_RET20, DATES
    log("下載財報、董監持股質押、外資持股、重大訊息…")
    EXTRA = load_extra(trading[-1][0])
    HIST2 = build_hist2(PREV_HIST2)
    DATES = [d.strftime("%m/%d") for d, _, _ in trading]
    TAIEX_RET20 = round((taiex[-1][1] / taiex[-21][1] - 1) * 100, 2) if len(taiex) > 21 else None
    log("計算技術指標與選股…")
    build_report(taiex, trading[-1][0])
    STATUS.update(state="ready", progress=100, report_time=datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
    log(f"完成！資料日期 {trading[-1][0]:%Y-%m-%d}，共 {len(hist)} 檔股票")
    cleanup_cache(trading[0][0])


def cleanup_cache(oldest):
    limit = oldest - timedelta(days=30)
    for f in os.listdir(DATA_DIR):
        try:
            if datetime.strptime(f[:8], "%Y%m%d").date() < limit:
                os.remove(os.path.join(DATA_DIR, f))
        except Exception:
            pass


# ---------------------------------------------------------------- 技術指標
def sma(a, n):
    out = [None] * len(a)
    s = 0.0
    for i, x in enumerate(a):
        s += x
        if i >= n:
            s -= a[i - n]
        if i >= n - 1:
            out[i] = s / n
    return out


def ema(a, n):
    out, k, e = [], 2 / (n + 1), None
    for x in a:
        e = x if e is None else x * k + e * (1 - k)
        out.append(e)
    return out


def rsi(c, n=14):
    out = [None] * len(c)
    if len(c) <= n:
        return out
    gains = [max(c[i] - c[i - 1], 0) for i in range(1, len(c))]
    losses = [max(c[i - 1] - c[i], 0) for i in range(1, len(c))]
    ag, al = sum(gains[:n]) / n, sum(losses[:n]) / n
    for i in range(n, len(c)):
        if i > n:
            ag = (ag * (n - 1) + gains[i - 1]) / n
            al = (al * (n - 1) + losses[i - 1]) / n
        out[i] = 100.0 if al == 0 else 100 - 100 / (1 + ag / al)
    return out


def kd(h, l, c, n=9):
    K, D, k, d_ = [], [], 50.0, 50.0
    for i in range(len(c)):
        lo, hi = min(l[max(0, i - n + 1):i + 1]), max(h[max(0, i - n + 1):i + 1])
        rsv = 50.0 if hi == lo else (c[i] - lo) / (hi - lo) * 100
        k = k * 2 / 3 + rsv / 3
        d_ = d_ * 2 / 3 + k / 3
        K.append(k); D.append(d_)
    return K, D


def atr(h, l, c, n=14):
    tr = [h[0] - l[0]] + [max(h[i] - l[i], abs(h[i] - c[i - 1]), abs(l[i] - c[i - 1])) for i in range(1, len(c))]
    out, a = [], None
    for i, x in enumerate(tr):
        a = x if a is None else (a * (n - 1) + x) / n
        out.append(a)
    return out


def tick(p):
    if p < 10: return 0.01
    if p < 50: return 0.05
    if p < 100: return 0.1
    if p < 500: return 0.5
    if p < 1000: return 1
    return 5


def rnd(p, mode="near"):
    if p is None or p <= 0:
        return None
    t = tick(p)
    f = {"near": round, "down": math.floor, "up": math.ceil}[mode]
    v = f(p / t) * t
    return round(v, 2)


def analyze(code):
    s = HIST.get(code)
    if not s or len(s["c"]) < 30:
        return None
    c, h, l, v = s["c"], s["h"], s["l"], s["v"]
    n = len(c)
    ma5, ma10, ma20, ma60 = sma(c, 5), sma(c, 10), sma(c, 20), sma(c, 60) if n >= 60 else [None] * n
    vma5, vma20 = sma(v, 5), sma(v, 20)
    r = rsi(c)
    K, D = kd(h, l, c)
    dif = [a - b for a, b in zip(ema(c, 12), ema(c, 26))]
    sig = ema(dif, 9)
    hist_ = [a - b for a, b in zip(dif, sig)]
    at = atr(h, l, c)
    # 布林通道寬度
    bw = [None] * n
    for i in range(19, n):
        seg = c[i - 19:i + 1]
        m = sum(seg) / 20
        sd = (sum((x - m) ** 2 for x in seg) / 20) ** 0.5
        bw[i] = 4 * sd / m if m else None
    bws = [x for x in bw[-60:] if x is not None]
    bw_rank = sum(1 for x in bws if x <= bw[-1]) / len(bws) if bws and bw[-1] is not None else 0.5
    m20 = ma20[-1]
    upper = m20 + 2 * (bw[-1] or 0) * m20 / 4 if m20 else None

    ins = INST.get(code, [])
    f5 = sum(x[1] for x in ins[-5:]); t5 = sum(x[2] for x in ins[-5:])
    f10 = sum(x[1] for x in ins[-10:]); t10 = sum(x[2] for x in ins[-10:])
    buy_days10 = sum(1 for x in ins[-10:] if x[1] + x[2] + x[3] > 0)
    trust_streak = 0
    for x in reversed(ins):
        if x[2] > 0: trust_streak += 1
        else: break
    foreign_streak = 0
    for x in reversed(ins):
        if x[1] > 0: foreign_streak += 1
        else: break

    prev = c[-2] if n >= 2 else c[-1]
    chg = c[-1] - prev
    pe, yld, pb = FUND.get(code, (None, None, None))
    return {
        "code": code, "name": s["name"], "market": s["market"], "date": s["dates"][-1],
        "close": c[-1], "open": s["o"][-1], "high": h[-1], "low": l[-1], "prev": prev,
        "chg": round(chg, 2), "chg_pct": round(chg / prev * 100, 2) if prev else 0,
        "vol": v[-1], "vma5": vma5[-1], "vma20": vma20[-1],
        "ma5": ma5[-1], "ma10": ma10[-1], "ma20": m20, "ma60": ma60[-1],
        "ma20_prev5": ma20[-6] if n >= 25 else None, "ma5_prev": ma5[-2],
        "rsi": r[-1], "k": K[-1], "d": D[-1], "k_prev": K[-2], "d_prev": D[-2],
        "macd": hist_[-1], "macd_prev": hist_[-2], "dif": dif[-1],
        "atr": at[-1], "bw_rank": bw_rank, "upper": upper,
        "high20": max(h[-20:]), "low20": min(l[-20:]), "high60": max(h[-60:]), "low10": min(l[-10:]),
        "close_above_ma20_days": next((i for i in range(min(n, 30)) if ma20[-1 - i] is None or c[-1 - i] < ma20[-1 - i]), 30),
        "f5": f5, "t5": t5, "f10": f10, "t10": t10, "buy_days10": buy_days10,
        "trust_streak": trust_streak, "foreign_streak": foreign_streak,
        "pe": pe, "yield": yld, "pb": pb,
        "spark": [round(x, 2) for x in c[-40:]],
        "ret5": round((c[-1] / c[-6] - 1) * 100, 2) if n >= 6 else None,
        "ret20": round((c[-1] / c[-21] - 1) * 100, 2) if n >= 21 else None,
        "days": n,
    }


def liquid(a):
    return a and not is_nonstock(a["code"]) and a["days"] >= 60 and a["close"] >= 10 and (a["vma20"] or 0) >= 800 and a["vol"] >= 300


def score_momentum(a):
    """今日推薦: 強勢多頭、量價齊揚"""
    sc, why = 0, []
    c = a["close"]
    if a["ma60"] and c > a["ma5"] > a["ma10"] > a["ma20"] > a["ma60"]:
        sc += 25; why.append("均線多頭排列 (5>10>20>60)")
    elif c > a["ma5"] > a["ma10"] > a["ma20"]:
        sc += 15; why.append("短中期均線多頭排列")
    else:
        return 0, why
    if a["ma20_prev5"] and a["ma20"] > a["ma20_prev5"]:
        sc += 8; why.append("月線上揚")
    vr = a["vol"] / a["vma20"] if a["vma20"] else 0
    if 1.3 <= vr <= 4:
        sc += 15; why.append(f"量增 {vr:.1f} 倍於月均量")
    elif vr > 4:
        sc += 5; why.append(f"爆量 {vr:.1f} 倍，留意追高風險")
    if a["rsi"] and 55 <= a["rsi"] <= 75:
        sc += 10; why.append(f"RSI {a['rsi']:.0f} 強勢區")
    elif a["rsi"] and a["rsi"] > 80:
        sc -= 15; why.append(f"RSI {a['rsi']:.0f} 過熱")
    if a["macd"] > 0 and a["macd"] > a["macd_prev"]:
        sc += 10; why.append("MACD 紅柱放大")
    if a["k"] > a["d"] and a["k_prev"] <= a["d_prev"] and a["k"] < 80:
        sc += 7; why.append("KD 黃金交叉")
    elif a["k"] > a["d"] and a["k"] < 85:
        sc += 3
    if c >= a["high20"] * 0.98:
        sc += 10; why.append("接近/突破 20 日新高")
    if a["f5"] + a["t5"] > 0:
        sc += 8; why.append(f"外資+投信 5 日買超 {a['f5'] + a['t5']:,} 張")
    if a["trust_streak"] >= 3:
        sc += 5; why.append(f"投信連買 {a['trust_streak']} 天")
    if 0 < a["chg_pct"] < 7:
        sc += 5
    elif a["chg_pct"] >= 9.5:
        sc -= 10; why.append("今日漲停，不宜追價，等回測")
    elif a["chg_pct"] < -2:
        sc -= 8
    bias = (c / a["ma20"] - 1) * 100
    if bias > 15:
        sc -= 15; why.append(f"月線乖離 {bias:.0f}% 偏大")
    return sc, why


def score_potential(a):
    """潛力股: 打底完成、籌碼默默進駐、波動收斂，可能即將發動"""
    sc, why = 0, []
    c, m20 = a["close"], a["ma20"]
    if not m20 or not a["ma60"]:
        return 0, why
    bias = (c / m20 - 1) * 100
    if not (-2 <= bias <= 6):
        return 0, why
    if 0 < a["close_above_ma20_days"] <= 5:
        sc += 20; why.append(f"剛站上月線 {a['close_above_ma20_days']} 天")
    elif bias >= 0:
        sc += 8
    if a["ma20_prev5"] and a["ma20"] >= a["ma20_prev5"]:
        sc += 10; why.append("月線走平翻揚")
    if a["bw_rank"] <= 0.25:
        sc += 18; why.append("布林通道收斂，蓄勢待發")
    elif a["bw_rank"] <= 0.4:
        sc += 8
    inst10 = a["f10"] + a["t10"]
    if inst10 > 0 and a["buy_days10"] >= 6:
        sc += 20; why.append(f"法人 10 日中 {a['buy_days10']} 天買超，累計 {inst10:,} 張")
    elif inst10 > 0:
        sc += 8; why.append(f"法人 10 日累計買超 {inst10:,} 張")
    if a["t10"] > 0 and a["trust_streak"] >= 2:
        sc += 6; why.append(f"投信連買 {a['trust_streak']} 天")
    if a["vma5"] and a["vma20"] and 1.0 < a["vma5"] / a["vma20"] < 2.5:
        sc += 8; why.append("成交量溫和放大")
    if a["rsi"] and 45 <= a["rsi"] <= 62:
        sc += 8; why.append(f"RSI {a['rsi']:.0f} 中性偏多，尚未過熱")
    if a["macd"] > a["macd_prev"] and a["macd_prev"] < 0.0005 * c:
        sc += 8; why.append("MACD 由綠轉紅 / 綠柱縮短")
    if a["pe"] and 0 < a["pe"] <= 20:
        sc += 5; why.append(f"本益比 {a['pe']:.1f} 合理")
    if a["yield"] and a["yield"] >= 4:
        sc += 4; why.append(f"殖利率 {a['yield']:.1f}%")
    room = (a["high60"] / c - 1) * 100
    if room >= 10:
        sc += 5; why.append(f"距 60 日高點仍有 {room:.0f}% 空間")
    if a["ret5"] is not None and a["ret5"] > 12:
        sc -= 10
    if a["chg_pct"] <= -3:
        sc -= 10; why.append(f"今日下跌 {a['chg_pct']}%，等止跌再進")
    return sc, why


def trade_plan(a, style):
    c, A = a["close"], a["atr"]
    if style == "momentum":
        entry_lo = max(a["ma5"], c - 0.8 * A)
        entry_hi = c + 0.2 * A
        stop = min(entry_lo - 1.0 * A, a["ma10"])
        stop = max(stop, c - 2.2 * A)
        t1 = c + 2 * A
        t2 = max(c + 3.5 * A, a["high60"])
    elif style == "potential":
        entry_lo = max(a["ma20"], c - 1.0 * A)
        entry_hi = c + 0.3 * A
        stop = min(a["ma20"] - 0.8 * A, a["low10"])
        stop = max(stop, c - 2.5 * A)
        t1 = max(a["upper"] or 0, c + 1.5 * A)
        t2 = max(a["high60"], c + 3 * A)
    elif style == "rebound":
        # 空頭: 等站回月線才進場
        entry_lo = a["ma20"]
        entry_hi = a["ma20"] + 0.3 * A
        stop = entry_lo - 1.2 * A
        t1 = entry_hi + 2 * A
        t2 = max(a["high60"], entry_hi + 3.5 * A)
    if entry_lo > entry_hi:
        entry_lo, entry_hi = entry_hi, entry_lo
    t2 = max(t2, t1 + 0.5 * A)
    mid = (entry_lo + entry_hi) / 2
    rr = (t1 - mid) / (mid - stop) if mid > stop else None
    return {"entry_lo": rnd(entry_lo, "down"), "entry_hi": rnd(entry_hi, "up"), "stop": rnd(stop, "down"),
            "t1": rnd(t1, "up"), "t2": rnd(t2, "up"), "rr": round(rr, 2) if rr else None,
            "stop_pct": round((stop / mid - 1) * 100, 1), "t1_pct": round((t1 / mid - 1) * 100, 1)}


def generic_plan(a):
    """任意個股查詢: 依目前型態給出建議"""
    c = a["close"]
    if a["ma20"] and c > a["ma20"] and a["ma5"] > a["ma20"]:
        p = trade_plan(a, "momentum"); trend = "多頭"
    elif a["ma20"] and c < a["ma20"] and a["ma5"] < a["ma20"]:
        p = trade_plan(a, "rebound"); trend = "空頭"
        p["note"] = "目前在月線之下，屬空方格局。建議等站回月線 {:.2f} 再考慮進場。".format(a["ma20"])
    else:
        p = trade_plan(a, "potential"); trend = "盤整"
    p["trend"] = trend
    return p


def pack(a, plan, sc, why):
    keep = ["code", "name", "market", "close", "chg", "chg_pct", "vol", "vma20", "ma5", "ma10", "ma20", "ma60",
            "rsi", "k", "d", "atr", "f5", "t5", "f10", "t10", "pe", "yield", "spark", "ret5", "ret20", "high60",
            "trust_streak", "foreign_streak", "date", "prev"]
    o = {k: (round(a[k], 2) if isinstance(a[k], float) else a[k]) for k in keep}
    o.update(score=sc, why=why, plan=plan)
    return o


def rr_adj(plan):
    """風報比太差的扣分"""
    rr = plan["rr"] or 0
    return -15 if rr < 1 else -5 if rr < 1.3 else 0


_SV = {}


def sv_of(a):
    if a["code"] not in _SV:
        f = fundamentals(a)
        ch = chip_structure(a["code"], a)
        sv = strength_vs_hype(a, f, ch)
        fh = fin_health(a["code"], a)
        card = scorecard(a, f, fh, ch, sv, price_patterns(a["code"], a))
        pe = f.get("pe") or (a["close"] / f["eps_base"] if f.get("eps_base") and f["eps_base"] > 0 else None)
        sv["row"] = [round(pe, 1) if pe else None, (f.get("div") or {}).get("yield"), round((f.get("mrev") or {}).get("cum_yoy") or 0, 1)
                     if (f.get("mrev") or {}).get("cum_yoy") is not None else None, fh.get("gm"), ch.get("mcap"), a.get("ret20"),
                     card["total"], card["grade"], sv["strength"], sv["hype"]]
        _SV[a["code"]] = sv
    return _SV[a["code"]]


def with_sv(o, a):
    sv = sv_of(a)
    o["sv"] = {k: sv[k] for k in ("strength", "hype", "hype_lv", "verdict", "vc")}
    o["grade"] = sv["row"][7]
    o["themes"] = themes_for(a["code"])
    o["news"] = news_for(a["code"])[:2]
    return o


def adjust_by_sv(a, s, w, momentum):
    """實力高的加分、炒作風險高的扣分；新聞熱門題材加分"""
    sv = sv_of(a)
    w = list(w)
    if sv["hype"] >= 50:
        s -= 20; w.append(f"炒作風險{sv['hype_lv']}，降低推薦")
    elif sv["hype"] >= 35 and momentum:
        s -= 8
    s += (sv["strength"] - 50) // 5
    for t in themes_for(a["code"]):
        s += 8; w.append(f"新聞題材：{t}")
    return s, w


_LAST_BUILD = {}


def build_report_again():
    if _LAST_BUILD:
        build_report(*_LAST_BUILD["args"])


def build_report(taiex, last_date):
    global REPORT
    _LAST_BUILD["args"] = (taiex, last_date)
    _SV.clear()
    all_a = {}
    for code in HIST:
        try:
            a = analyze(code)
        except Exception:
            a = None
        if a:
            all_a[code] = a
    latest = [a for a in all_a.values() if a["date"] == last_date.strftime("%Y-%m-%d")]

    mom, pot = [], []
    for a in latest:
        if not liquid(a):
            continue
        s, w = score_momentum(a)
        s += rr_adj(trade_plan(a, "momentum"))
        if s >= 45:
            s, w = adjust_by_sv(a, s, w, momentum=True)
        if s >= 60:
            mom.append((s, a, w))
    mom.sort(key=lambda x: -x[0])
    mom = mom[:12]
    mom_codes = {a["code"] for _, a, _ in mom}
    for a in latest:
        if not liquid(a) or a["code"] in mom_codes:
            continue
        s, w = score_potential(a)
        s += rr_adj(trade_plan(a, "potential"))
        if s >= 40:
            s, w = adjust_by_sv(a, s, w, momentum=False)
        if s >= 55:
            pot.append((s, a, w))
    pot.sort(key=lambda x: -x[0])
    pot = pot[:12]

    up = sum(1 for a in latest if a["chg"] > 0)
    down = sum(1 for a in latest if a["chg"] < 0)
    tradable = [a for a in latest if a["vol"] >= 500 and not is_nonstock(a["code"])]
    gainers = sorted(tradable, key=lambda a: -a["chg_pct"])[:10]
    losers = sorted(tradable, key=lambda a: a["chg_pct"])[:10]
    by_value = sorted([a for a in latest if not is_nonstock(a["code"])], key=lambda a: -(a["vol"] * a["close"]))[:10]
    foreign_buy = sorted(latest, key=lambda a: -a["f5"])[:10]

    # 大盤多空判斷
    market = {"taiex": None}
    if taiex:
        closes = [x[1] for x in taiex]
        m20 = sum(closes[-20:]) / min(20, len(closes))
        m60 = sum(closes[-60:]) / min(60, len(closes))
        last = taiex[-1]
        if last[1] > m20 > m60:
            mood, pos = "多頭", "可維持 6~8 成資金部位，順勢操作"
        elif last[1] > m20:
            mood, pos = "偏多震盪", "建議 4~6 成部位，分批進場"
        elif last[1] > m60:
            mood, pos = "短線轉弱", "建議 3~4 成部位，嚴設停損，減少追高"
        else:
            mood, pos = "空頭", "建議 2 成以下部位，以觀望為主"
        market = {"taiex": last[1], "taiex_chg_pct": last[2], "ma20": round(m20, 2), "ma60": round(m60, 2),
                  "mood": mood, "position": pos, "series": [[x[0], x[1]] for x in taiex]}

    simple = lambda a: {"code": a["code"], "name": a["name"], "market": a["market"], "close": a["close"],
                        "chg_pct": a["chg_pct"], "vol": a["vol"], "f5": a["f5"], "t5": a["t5"],
                        "value": round(a["vol"] * a["close"] / 1e5, 1)}
    REPORT = {
        "date": last_date.strftime("%Y-%m-%d"),
        "dates": DATES[-60:],
        "generated": datetime.now().strftime("%Y-%m-%d %H:%M"),
        "market": market,
        "breadth": {"up": up, "down": down, "flat": len(latest) - up - down},
        "momentum": [with_sv(pack(a, trade_plan(a, "momentum"), s, w), a) for s, a, w in mom],
        "potential": [with_sv(pack(a, trade_plan(a, "potential"), s, w), a) for s, a, w in pot],
        "news": {k: NEWS.get(k) for k in ("date", "market", "global", "themes", "headlines")} if NEWS else None,
        "gainers": [simple(a) for a in gainers],
        "losers": [simple(a) for a in losers],
        "by_value": [simple(a) for a in by_value],
        "foreign_buy": [simple(a) for a in foreign_buy],
        "daytrade": daytrade_list(latest),
        "divs": div_list(latest),
        "etfs": etf_list(latest),
        "nolimit": nolimit_list(all_a, last_date),
        "all": [[a["code"], a["name"], a["market"], sec_type(a["code"]) if is_nonstock(a["code"]) else (PROFILE.get(a["code"]) or {}).get("ind") or "", a["close"],
                 a["chg_pct"], a["vol"], sv_of(a)["verdict"], sv_of(a)["vc"]] + sv_of(a)["row"]
                for a in sorted(latest, key=lambda x: x["code"])],
    }


# ---------------------------------------------------------------- 公司基本面資料
INDUSTRY = {"01": "水泥工業", "02": "食品工業", "03": "塑膠工業", "04": "紡織纖維", "05": "電機機械", "06": "電器電纜",
            "08": "玻璃陶瓷", "09": "造紙工業", "10": "鋼鐵工業", "11": "橡膠工業", "12": "汽車工業", "14": "建材營造",
            "15": "航運業", "16": "觀光餐旅", "17": "金融保險", "18": "貿易百貨", "19": "綜合", "20": "其他",
            "21": "化學工業", "22": "生技醫療業", "23": "油電燃氣業", "24": "半導體業", "25": "電腦及週邊設備業",
            "26": "光電業", "27": "通信網路業", "28": "電子零組件業", "29": "電子通路業", "30": "資訊服務業",
            "31": "其他電子業", "32": "文化創意業", "33": "農業科技業", "34": "電子商務", "35": "綠能環保",
            "36": "數位雲端", "37": "運動休閒", "38": "居家生活", "80": "管理股票"}
PROFILE = {}   # code -> 公司資料 / EPS / 營收 / 股利
IND_PE = {}    # 產業 -> 本益比中位數


def fetch_list(url):
    try:
        r = http_get(url, timeout=60)
        return r if isinstance(r, list) else []
    except Exception as e:
        print("  ! 下載失敗", url, e)
        return []


def roc_date(s):
    """1151028 -> 2026/10/28；19501229 -> 1950/12/29"""
    s = (s or "").strip()
    if len(s) == 7 and s.isdigit():
        return f"{int(s[:3]) + 1911}/{s[3:5]}/{s[5:]}"
    if len(s) == 8 and s.isdigit():
        return f"{s[:4]}/{s[4:6]}/{s[6:]}"
    return s


def load_profiles():
    today = date.today()
    cached = load_cache("prof", today)
    if cached:
        return cached
    tw, tp = "https://openapi.twse.com.tw/v1/", "https://www.tpex.org.tw/openapi/v1/"
    prof = {}

    def P(code):
        return prof.setdefault(code.strip(), {})

    for r in fetch_list(tw + "opendata/t187ap03_L"):
        P(r["公司代號"]).update(full=r.get("公司名稱"), ind=INDUSTRY.get(r.get("產業別", "").strip(), ""),
                            chair=r.get("董事長"), gm=r.get("總經理"), found=roc_date(r.get("成立日期")),
                            listed=roc_date(r.get("上市日期")), cap=num(r.get("實收資本額")),
                            shares=num(r.get("已發行普通股數或TDR原股發行股數")), web=(r.get("網址") or "").strip(),
                            en=r.get("英文簡稱"))
    for r in fetch_list(tp + "mopsfin_t187ap03_O"):
        P(r["SecuritiesCompanyCode"]).update(full=r.get("CompanyName"), ind=INDUSTRY.get(r.get("SecuritiesIndustryCode", "").strip(), ""),
                                             chair=r.get("Chairman"), gm=r.get("GeneralManager"),
                                             found=roc_date(r.get("DateOfIncorporation")), listed=roc_date(r.get("DateOfListing")),
                                             cap=num(r.get("Paidin.Capital.NTDollars")), shares=num(r.get("IssueShares")),
                                             web=(r.get("WebAddress") or "").strip(" 　"), en=(r.get("Symbol") or "").strip(" 　"))
    # 今年累計 EPS 與損益 (千元)
    for url, kc, ky, ke in ((tw + "opendata/t187ap14_L", "公司代號", "年度", "基本每股盈餘(元)"),
                            (tp + "mopsfin_t187ap14_O", "SecuritiesCompanyCode", "Year", "基本每股盈餘")):
        for r in fetch_list(url):
            p = P(r[kc])
            if r.get("產業別"):
                p["ind"] = r["產業別"]
            p["eps"] = {"y": int(r.get(ky) or 0) + 1911, "q": int(r.get("季別") or 0), "eps": num(r.get(ke)),
                        "rev": num(r.get("營業收入")), "op": num(r.get("營業利益")), "ni": num(r.get("稅後淨利"))}
    # 最新月營收 (千元)
    for url in (tw + "opendata/t187ap05_L", tp + "mopsfin_t187ap05_O"):
        for r in fetch_list(url):
            ym = r.get("資料年月", "")
            note = (r.get("備註") or "").strip()
            P(r["公司代號"])["mrev"] = {
                "ym": f"{int(ym[:3]) + 1911}/{ym[3:]}" if len(ym) == 5 else ym, "rev": num(r.get("營業收入-當月營收")),
                "mom": num(r.get("營業收入-上月比較增減(%)")), "yoy": num(r.get("營業收入-去年同月增減(%)")),
                "cum": num(r.get("累計營業收入-當月累計營收")), "cum_yoy": num(r.get("累計營業收入-前期比較增減(%)")),
                "note": "" if note in ("-", "無", "無。", "不適用") else note}
    # 上市股利分派 (元/股)
    for r in fetch_list(tw + "opendata/t187ap45_L"):
        cash = sum(num(r.get(k)) or 0 for k in ("股東配發-盈餘分配之現金股利(元/股)", "股東配發-法定盈餘公積發放之現金(元/股)",
                                                "股東配發-資本公積發放之現金(元/股)"))
        stock = sum(num(r.get(k)) or 0 for k in ("股東配發-盈餘轉增資配股(元/股)", "股東配發-法定盈餘公積轉增資配股(元/股)",
                                                 "股東配發-資本公積轉增資配股(元/股)"))
        P(r["公司代號"]).setdefault("divs", []).append(
            {"year": int(r.get("股利年度") or 0) + 1911, "period": r.get("股利所屬年(季)度", ""), "cash": round(cash, 4),
             "stock": round(stock, 4), "status": r.get("決議（擬議）進度", ""), "board": roc_date(r.get("董事會（擬議）股利分派日"))})
    # 上櫃: 最近年度現金股利
    for r in fetch_list(tp + "tpex_mainboard_peratio_analysis"):
        dps = num(r.get("DividendPerShare"))
        if dps:
            P(r["SecuritiesCompanyCode"]).setdefault("dps", dps)
    # 除權息預告
    for r in fetch_list(tw + "exchangeReport/TWT48U_ALL"):
        P(r["Code"])["ex"] = {"date": roc_date(r.get("Date")), "type": "除" + (r.get("Exdividend") or ""),
                              "cash": num(r.get("CashDividend")), "stock_ratio": num(r.get("StockDividendRatio"))}
    for r in fetch_list(tp + "tpex_exright_prepost"):
        P(r["SecuritiesCompanyCode"])["ex"] = {"date": roc_date(r.get("ExRrightsExDividendDate")),
                                               "type": r.get("ExRrightsExDividend"), "cash": num(r.get("CashDividend")),
                                               "stock_ratio": num(r.get("StockDividendRatio"))}
    for r in fetch_list(tp + "tpex_exright_daily"):   # 已公告、即將除息（含 ETF）
        code = r.get("SecuritiesCompanyCode")
        if code and not P(code).get("ex"):
            P(code)["ex"] = {"date": roc_date(r.get("Date")), "type": r.get("ExRightsDiviend"), "cash": num(r.get("CashDividend")),
                             "stock_ratio": None}
    prof = {c: p for c, p in prof.items() if is_stock_code(c)}
    if len(prof) > 500:
        save_cache("prof", today, prof)
    return prof


def compute_ind_pe():
    by = {}
    for code, p in PROFILE.items():
        pe = (FUND.get(code) or (None,))[0]
        if p.get("ind") and pe and 0 < pe < 200:
            by.setdefault(p["ind"], []).append(pe)
    out = {}
    for ind, xs in by.items():
        xs.sort()
        out[ind] = xs[len(xs) // 2]
    return out


def dividend_summary(code, close):
    """最近一個股利年度的現金股利、股票股利合計"""
    p = PROFILE.get(code, {})
    divs = p.get("divs") or []
    rows, cash, stock, year = [], None, 0.0, None
    if divs:
        order = {"第1季": 1, "上半年": 2, "第2季": 2, "第3季": 3, "第4季": 4, "下半年": 4, "年度": 5}
        divs = sorted(divs, key=lambda d: (d["year"], order.get(d["period"].strip(), 5)), reverse=True)
        if any("季" in d["period"] for d in divs[:2]):
            rows = [d for d in divs if "季" in d["period"]][:4]      # 季配息: 近四季合計
        elif any("半年" in d["period"] for d in divs[:2]):
            rows = [d for d in divs if "半年" in d["period"]][:2]    # 半年配: 近兩次
        else:
            rows = [d for d in divs if d["year"] == divs[0]["year"]]
        year = rows[0]["year"]
        cash = round(sum(d["cash"] for d in rows), 4)
        stock = round(sum(d["stock"] for d in rows), 4)
    elif p.get("dps"):
        cash = p["dps"]
    ex = p.get("ex")
    if ex and ex.get("stock_ratio"):
        # 預告表的配股率是「每股配幾股」，換算成元
        stock = max(stock, round(ex["stock_ratio"] * 10, 4))
    out = {"year": year, "rows": rows, "cash": cash, "stock": stock, "ex": ex}
    if cash is not None and close:
        out["yield"] = round(cash / close * 100, 2)
    if (cash or stock) and close:
        # 除權息參考價 = (股價 - 現金股利) / (1 + 股票股利/10)
        out["ref_price"] = round((close - (cash or 0)) / (1 + stock / 10), 2)
    return out


def fundamentals(a):
    code, c = a["code"], a["close"]
    p = PROFILE.get(code, {})
    pe, yld, pb = FUND.get(code, (None, None, None))
    e = p.get("eps") or {}
    f = {"ind": sec_type(code) if is_nonstock(code) else (p.get("ind") or ""), "pe": pe, "pb": pb, "ind_pe": IND_PE.get(p.get("ind") or "")}
    if pe and pe > 0:
        f["eps_ttm"] = round(c / pe, 2)
    if e.get("eps") is not None and e.get("q"):
        f["eps_cum"], f["eps_q"], f["eps_y"] = e["eps"], e["q"], e["y"]
        f["eps_est"] = round(e["eps"] * 4 / e["q"], 2)
        if e.get("rev"):
            f["op_margin"] = round(e["op"] / e["rev"] * 100, 1) if e.get("op") is not None else None
            f["net_margin"] = round(e["ni"] / e["rev"] * 100, 1) if e.get("ni") is not None else None
    d = dividend_summary(code, c)
    f["div"] = d
    base = f.get("eps_est") if f.get("eps_est") is not None else f.get("eps_ttm")
    if base is not None:
        f["eps_base"] = base
        if d["stock"]:
            f["eps_after_stock"] = round(base / (1 + d["stock"] / 10), 2)   # 配股後股本膨脹，EPS 被稀釋
        if d["cash"] and f.get("eps_ttm"):
            f["payout"] = round(d["cash"] / f["eps_ttm"] * 100, 0)
    f["mrev"] = p.get("mrev")
    return f


def analyst_report(a, f, plan):
    """依基本面 / 技術面 / 籌碼面，產生分析師風格的評等與說明"""
    c, pts = a["close"], 0
    fund_pts, tech_pts, chip_pts, risks = [], [], [], []
    m = f.get("mrev") or {}
    # 成長性
    if m.get("cum_yoy") is not None:
        g = m["cum_yoy"]
        if g >= 20: pts += 2; fund_pts.append(f"今年累計營收年增 {g:.1f}%，成長動能強勁")
        elif g >= 5: pts += 1; fund_pts.append(f"今年累計營收年增 {g:.1f}%，穩健成長")
        elif g >= 0: fund_pts.append(f"今年累計營收年增 {g:.1f}%，營運持平")
        elif g > -5: fund_pts.append(f"今年累計營收小幅年減 {abs(g):.1f}%，營運持平偏弱")
        else: pts -= 2; fund_pts.append(f"今年累計營收年減 {abs(g):.1f}%，基本面轉弱"); risks.append("營收衰退")
        if m.get("yoy") is not None:
            yy, mm = m["yoy"], m["mom"] or 0
            fund_pts.append(f"{m['ym']} 單月營收{'年增' if yy >= 0 else '年減'} {abs(yy):.1f}%、{'月增' if mm >= 0 else '月減'} {abs(mm):.1f}%"
                            + (f"（公司說明：{m['note']}）" if m.get("note") else ""))
    # 獲利能力
    if f.get("eps_cum") is not None:
        txt = f"{f['eps_y']} 年前 {f['eps_q']} 季 EPS {f['eps_cum']:.2f} 元，全年化約 {f['eps_est']:.2f} 元"
        if f.get("op_margin") is not None:
            txt += f"，營業利益率 {f['op_margin']}%"
        fund_pts.append(txt)
        if f["eps_cum"] < 0: pts -= 2; risks.append("目前處於虧損")
        if (f.get("op_margin") or 0) >= 20: pts += 1
    # 評價
    pe, ind_pe = f.get("pe"), f.get("ind_pe")
    if not pe and f.get("eps_base") and f["eps_base"] > 0:
        pe = c / f["eps_base"]          # 用全年化 EPS 推估本益比
    target = None
    if pe and ind_pe:
        rel = pe / ind_pe
        if rel < 0.8: pts += 2; fund_pts.append(f"本益比 {pe:.1f} 倍，低於同業中位數 {ind_pe:.1f} 倍，評價具吸引力")
        elif rel <= 1.2: fund_pts.append(f"本益比 {pe:.1f} 倍，與同業中位數 {ind_pe:.1f} 倍相當")
        elif rel <= 1.6: pts -= 1; fund_pts.append(f"本益比 {pe:.1f} 倍，略高於同業 {ind_pe:.1f} 倍，市場已反映部分成長")
        else: pts -= 2; fund_pts.append(f"本益比 {pe:.1f} 倍，明顯高於同業 {ind_pe:.1f} 倍，評價偏高"); risks.append("評價偏高，業績不如預期時修正幅度大")
    elif not pe:
        risks.append("近四季無獲利或無本益比資料，無法用本益比評價")
    if f.get("eps_base") and f["eps_base"] > 0 and ind_pe:
        fair_pe = min(max(ind_pe, 8), 30)
        g = m.get("cum_yoy")
        if g is not None and g >= 20: fair_pe *= 1.15
        elif g is not None and g < -5: fair_pe *= 0.85
        target = rnd(f["eps_base"] * fair_pe)
    # 股利
    d = f.get("div") or {}
    if d.get("yield"):
        if d["yield"] >= 5: pts += 1; fund_pts.append(f"現金殖利率 {d['yield']}%，屬高殖利率股")
        else: fund_pts.append(f"現金殖利率 {d['yield']}%")
    if d.get("stock"):
        fund_pts.append(f"配發股票股利 {d['stock']} 元（每千股配 {d['stock'] * 100:.0f} 股），股本膨脹 {d['stock'] * 10:.1f}%，"
                        f"配股後 EPS 約 {f.get('eps_after_stock', '-')} 元")
    # 技術面
    if plan["trend"] == "多頭":
        pts += 2; tech_pts.append(f"股價站穩月線 {a['ma20']:.2f} 之上，短中期趨勢偏多")
    elif plan["trend"] == "空頭":
        pts -= 2; tech_pts.append(f"股價跌破月線 {a['ma20']:.2f}，趨勢偏空，宜等待止跌訊號"); risks.append("技術面空頭排列")
    else:
        tech_pts.append("股價於月線附近整理，方向尚待確認")
    if a.get("ma60"):
        tech_pts.append(f"季線 {a['ma60']:.2f}，股價{'在季線之上，長線結構仍佳' if c > a['ma60'] else '在季線之下，長線偏弱'}")
    if a["rsi"] is not None:
        r = a["rsi"]
        tech_pts.append(f"RSI {r:.0f}" + ("，已進入超買區，短線易震盪" if r > 75 else "，超賣區，留意反彈" if r < 30 else ""))
        if r > 80: risks.append("短線漲多、指標過熱")
    tech_pts.append(f"近 20 日區間 {a['low20']:.2f} ~ {a['high20']:.2f}，60 日高點 {a['high60']:.2f}")
    # 籌碼面
    inst10 = a["f10"] + a["t10"]
    chip_pts.append(f"外資近 10 日{'買超' if a['f10'] >= 0 else '賣超'} {abs(a['f10']):,} 張，投信{'買超' if a['t10'] >= 0 else '賣超'} {abs(a['t10']):,} 張")
    if a["trust_streak"] >= 3: chip_pts.append(f"投信連續買超 {a['trust_streak']} 天，有作帳/認養跡象")
    if a["foreign_streak"] >= 3: chip_pts.append(f"外資連續買超 {a['foreign_streak']} 天")
    pts += 1 if inst10 > 0 else -1
    if (a["vma20"] or 0) < 500: risks.append("成交量偏低，流動性風險")
    # 目標價 / 評等
    upside = round((target / c - 1) * 100, 1) if target else None
    if upside is not None:
        if upside >= 20: pts += 1
        elif upside <= -25: pts -= 2; risks.append(f"股價高於基本面估算合理價 {abs(upside):.0f}%")
        elif upside <= -10: pts -= 1
    if pts >= 5: rating, rc = "買進", "up"
    elif pts >= 2: rating, rc = "逢低布局", "up"
    elif pts >= -1: rating, rc = "中立", ""
    else: rating, rc = "觀望 / 減碼", "down"
    if (f.get("eps_cum") or 0) < 0 and rating in ("買進", "逢低布局"):
        rating, rc = "中立", ""      # 虧損公司不給買進評等
    summary = f"{a['name']}屬{f.get('ind') or '—'}，"
    summary += {"買進": "基本面與技術面同步轉強，建議積極布局。", "逢低布局": "整體條件偏正向，建議於支撐附近分批承接。",
                "中立": "多空因素交錯，建議區間操作或等待更明確訊號。", "觀望 / 減碼": "目前風險大於機會，建議暫時觀望，持有者控管部位。"}[rating]
    if target:
        summary += f" 以全年化 EPS {f['eps_base']:.2f} 元 × 合理本益比估算，合理價約 {target}（{'+' if upside >= 0 else ''}{upside}%）。"
    if is_nonstock(a["code"]):
        rating, rc = {"多頭": ("逢低布局", "up"), "空頭": ("觀望 / 減碼", "down")}.get(plan["trend"], ("中立", ""))
        lev = a["code"].endswith(("L", "R"))
        t = sec_type(a["code"])
        desc = {"ETF": "槓桿 / 反向型，只適合短線" if lev else "一次買進一籃子股票", "特別股": "特別股，通常有固定股息、價格波動小", "ETN": "券商發行的指數投資證券，有到期日與信用風險",
                "REIT": "不動產投資信託，收益來自租金", "TDR": "外國公司在台灣發行的存託憑證"}.get(t, t)
        summary = (f"{a['name']}是{t}（{desc}），沒有一般公司的完整財報分析。"
                   f"目前趨勢「{plan['trend']}」，" + {"逢低布局": "可在支撐附近分批買進。", "觀望 / 減碼": "建議等站回月線再考慮。", "中立": "可以定期定額或區間操作。"}[rating])
        fund_pts = [f"{t}沒有一般公司的財報評分，主要看價格趨勢、配息與成交量"]
        target, upside = None, None
        risks = ["槓桿 / 反向 ETF 長期持有會有耗損"] if lev else risks
    return {"rating": rating, "rc": rc, "points": pts, "target": target, "upside": upside, "summary": summary,
            "fund": fund_pts, "tech": tech_pts, "chip": chip_pts, "risks": risks or ["無明顯重大風險，仍須注意大盤系統性風險"]}


def stock_detail(code):
    a = analyze(code)
    if not a:
        return None
    p = generic_plan(a)
    sm, wm = score_momentum(a)
    sp, wp = score_potential(a)
    o = pack(a, p, max(sm, sp), wm if sm >= sp else wp)
    f = fundamentals(a)
    pr = PROFILE.get(code, {})
    o["prof"] = {k: pr.get(k) for k in ("full", "chair", "gm", "found", "listed", "web", "en")}
    o["prof"]["cap"] = round(pr["cap"] / 1e8, 2) if pr.get("cap") else None
    o["prof"]["shares"] = round(pr["shares"] / 1e8, 2) if pr.get("shares") else None
    o["fund"] = f
    o["rep"] = analyst_report(a, f, p)
    o["chip2"] = chip_structure(code, a)
    o["sv"] = strength_vs_hype(a, f, o["chip2"])
    rp, sv = o["rep"], o["sv"]
    if sv["verdict"] == "疑似炒作":     # 炒作風險高時，評等一律降為觀望
        rp.update(rating="觀望 / 減碼", rc="down")
        rp["summary"] = f"{a['name']}出現多項炒作警訊（炒作風險 {sv['hype']} 分），股價可能由短線資金推動，不建議追價。" + \
            (f" 基本面估算合理價約 {rp['target']}。" if rp.get("target") else "")
    elif sv["verdict"] == "有實力但短線過熱" and rp["rating"] == "買進":
        rp["rating"] = "逢低布局"
        rp["summary"] += " 惟短線過熱，宜等拉回再進場。"
    o["news"] = news_for(code)
    o["themes"] = themes_for(code)
    for k in ("low20", "high20"):
        o[k] = a[k]
    o["fh"] = fh = fin_health(code, a)
    o["pat"] = pat = price_patterns(code, a)
    o["card"] = scorecard(a, f, fh, o["chip2"], sv, pat)
    o["etf"] = is_nonstock(code)
    o["stype"] = sec_type(code)
    o["dt"] = daytrade_info(a)
    o["dv"] = div_analysis(a)
    if code in NOLIM:
        o["nolim"] = nolimit_reason(code, None)[1]
    s = HIST[code]
    k = min(60, len(s["c"]))
    o["ohlc"] = [[s["o"][i], s["h"][i], s["l"][i], s["c"][i], s["v"][i]] for i in range(len(s["c"]) - k, len(s["c"]))]
    o.pop("spark", None)
    return o


# ---------------------------------------------------------------- 籌碼結構 / 炒作警訊
RISK = {}      # 最新一日: 當沖、融資券、注意/處置、節目推介、集保大戶
HIST2 = {"mg": {}, "tdcc": {}}   # 融資餘額、集保大戶的歷史(用來算變化)
NEWS = {}      # 由雲端排程整理的新聞 (news.json)
PREV_HIST2 = {}  # 上一次雲端版網頁內嵌的歷史


def roc_period_end(s):
    """'115/10/20～115/10/27' 或 '1151022~1151029' -> date(迄日)"""
    s = (s or "").replace("～", "~").split("~")[-1].strip().replace("/", "")
    try:
        if len(s) == 7:
            return date(int(s[:3]) + 1911, int(s[3:5]), int(s[5:]))
    except ValueError:
        pass
    return None


def fetch_tdcc():
    """集保戶股權分散表(每週): code -> [千張大戶%, 400張以上%, 股東人數, 50張以下散戶%]"""
    url = "https://opendata.tdcc.com.tw/getOD.ashx?id=1-5"
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=90, context=SSL_CTX) as r:
        text = r.read().decode("utf-8-sig", "replace")
    out, ddate = {}, None
    for line in text.splitlines()[1:]:
        p = line.split(",")
        if len(p) < 6:
            continue
        code = p[1].strip()
        if not is_stock_code(code):
            continue
        ddate = p[0].strip()
        lv, pct = int(p[2]), num(p[5]) or 0
        o = out.setdefault(code, [0.0, 0.0, 0, 0.0])
        if lv == 15: o[0] += pct
        if 12 <= lv <= 15: o[1] += pct
        if lv <= 8: o[3] += pct
        if lv == 17: o[2] = int(num(p[3]) or 0)
    return {"date": ddate, "data": {c: [round(v[0], 2), round(v[1], 2), v[2], round(v[3], 2)] for c, v in out.items()}}


def load_risk(d):
    c = load_cache("risk3", d)
    if c:
        return c
    tw, tp = "https://openapi.twse.com.tw/v1/", "https://www.tpex.org.tw/openapi/v1/"
    dt, mg, flags, tv = {}, {}, {}, []
    # 當沖成交量 (張)
    try:
        js = http_get(f"https://www.twse.com.tw/rwd/zh/dayTrading/TWTB4U?date={d:%Y%m%d}&selectType=All&response=json")
        for t in js.get("tables", []):
            if "證券代號" in (t.get("fields") or []):
                for row in t["data"]:
                    if is_stock_code(row[0].strip()):
                        dt[row[0].strip()] = round((num(row[3]) or 0) / 1000)
    except Exception as e:
        print("  ! 上市當沖資料失敗", e)
    try:
        js = http_get(f"https://www.tpex.org.tw/www/zh-tw/intraday/stat?type=Daily&date={d:%Y}%2F{d:%m}%2F{d:%d}&response=json")
        for t in js.get("tables", []):
            if "證券代號" in (t.get("fields") or []):
                for row in t["data"]:
                    if is_stock_code(row[0].strip()):
                        dt[row[0].strip()] = round((num(row[3]) or 0) / 1000)
    except Exception as e:
        print("  ! 上櫃當沖資料失敗", e)
    # 融資融券 (張): [融資餘額, 融資前日餘額, 融資限額, 融券餘額]
    for r in fetch_list(tw + "exchangeReport/MI_MARGN"):
        code = r.get("股票代號", "").strip()
        if is_stock_code(code):
            mg[code] = [num(r.get("融資今日餘額")) or 0, num(r.get("融資前日餘額")) or 0, num(r.get("融資限額")) or 0,
                        num(r.get("融券今日餘額")) or 0]
    for r in fetch_list(tp + "tpex_mainboard_margin_balance"):
        code = r.get("SecuritiesCompanyCode", "").strip()
        if is_stock_code(code):
            mg[code] = [num(r.get("MarginPurchaseBalance")) or 0, num(r.get("MarginPurchaseBalancePreviousDay")) or 0,
                        num(r.get("MarginPurchaseQuota")) or 0, num(r.get("ShortSaleBalance")) or 0]
    # 注意股 / 處置股 / 投資理財節目異常推介
    def flag(code, kind, text):
        code = (code or "").strip()
        if is_stock_code(code):
            flags.setdefault(code, []).append([kind, text.strip()])
    for r in fetch_list(tw + "announcement/punish") + fetch_list(tp + "tpex_disposal_information"):
        code = r.get("Code") or r.get("SecuritiesCompanyCode")
        period = r.get("DispositionPeriod", "")
        end = roc_period_end(period)
        kind = "處置" if not end or end >= d else "近期處置"
        flag(code, kind, f"{period}（{r.get('ReasonsOfDisposition') or r.get('DispositionReasons') or ''}）")
    for r in fetch_list(tw + "announcement/notice"):
        flag(r.get("Code"), "注意", r.get("TradingInfoForAttention", ""))
    for r in fetch_list(tp + "tpex_trading_warning_information"):
        flag(r.get("SecuritiesCompanyCode"), "注意", r.get("TradingInformation", ""))
    for r in fetch_list(tw + "announcement/notetrans"):
        flag(r.get("Code"), "注意累計", r.get("RecentlyMetAttentionSecuritiesCriteria", ""))
    for r in fetch_list(tw + "Announcement/BFZFZU_T"):
        code = (r.get("Code") or "").strip()
        if is_stock_code(code):
            tv.append(code)
    try:
        tdcc = fetch_tdcc()
    except Exception as e:
        print("  ! 集保股權分散資料失敗", e)
        tdcc = {"date": None, "data": {}}
    c = {"dt": dt, "mg": mg, "flags": flags, "tv": tv, "tdcc": tdcc}
    if mg:
        save_cache("risk3", d, c)
    return c


def build_hist2(prev):
    """把各天的融資餘額、各週集保大戶比例串成歷史，用來看變化"""
    mgh, tdh = {}, {}
    for code, rows in (prev or {}).get("mg", {}).items():
        mgh[code] = {r[0]: r[1] for r in rows}
    for code, rows in (prev or {}).get("tdcc", {}).items():
        tdh[code] = {r[0]: r[1] for r in rows}
    for fn in sorted(os.listdir(DATA_DIR)):
        if not (fn.endswith("_risk.json") or fn.endswith("_risk2.json") or fn.endswith("_risk3.json")):
            continue
        try:
            with open(os.path.join(DATA_DIR, fn), encoding="utf-8") as fh:
                c = json.load(fh)
        except Exception:
            continue
        ds = fn[:8]
        for code, v in c.get("mg", {}).items():
            mgh.setdefault(code, {})[ds] = v[0]
        td = c.get("tdcc") or {}
        if td.get("date"):
            for code, v in td["data"].items():
                tdh.setdefault(code, {})[td["date"]] = v
    return {"mg": {c: sorted(v.items())[-6:] for c, v in mgh.items()},
            "tdcc": {c: sorted(v.items())[-4:] for c, v in tdh.items()},
            "mat": merge_events(prev, "mat"), "ins": merge_events(prev, "ins")}


def chip_structure(code, a):
    p = PROFILE.get(code, {})
    shares = p.get("shares")
    out = {}
    if shares:
        out["mcap"] = round(shares * a["close"] / 1e8, 1)                 # 市值(億)
        out["turnover"] = round(a["vol"] * 1000 / shares * 100, 2)        # 當日週轉率%
    dtv = RISK.get("dt", {}).get(code)
    if dtv is not None and a["vol"]:
        out["daytrade"] = round(dtv / a["vol"] * 100, 1)                  # 當沖比%
    m = RISK.get("mg", {}).get(code)
    if m:
        out["margin"], out["margin_chg"] = m[0], m[0] - m[1]
        out["margin_use"] = round(m[0] / m[2] * 100, 1) if m[2] else None
        out["short"] = m[3]
        out["short_ratio"] = round(m[3] / m[0] * 100, 1) if m[0] else None   # 券資比
        h = HIST2["mg"].get(code) or []
        if len(h) >= 3:
            out["margin_chg_n"] = [len(h) - 1, m[0] - h[0][1]]
    td = RISK.get("tdcc", {}).get("data", {}).get(code)
    if td:
        out["big1000"], out["big400"], out["holders"], out["retail"] = td
        out["tdcc_date"] = roc_date(RISK["tdcc"].get("date"))
        h = HIST2["tdcc"].get(code) or []
        if len(h) >= 2 and h[-1][0] != h[-2][0]:
            out["big1000_chg"] = round(h[-1][1][0] - h[-2][1][0], 2)
            out["holders_chg"] = h[-1][1][2] - h[-2][1][2]
    out["flags"] = RISK.get("flags", {}).get(code, [])
    out["tv"] = code in set(RISK.get("tv", []))
    return out


def news_for(code):
    return (NEWS.get("stocks") or {}).get(code) or []


def themes_for(code):
    return [t["name"] for t in (NEWS.get("themes") or []) if code in (t.get("codes") or [])]


def strength_vs_hype(a, f, ch):
    """判斷是真有實力，還是人為炒作 / 題材炒作"""
    if is_nonstock(a["code"]):
        t = sec_type(a["code"])
        checks = [["ok", "ETF 一次買進一籃子股票，風險分散，不易被單一主力炒作"]] if t == "ETF" else [["ok", f"這是{t}，不是一般普通股，請注意它的特性"]]
        if a["code"].endswith(("L", "R")):
            checks.append(["warn", "這是槓桿或反向型 ETF，只適合短線，長期持有會有耗損"])
        if (ch.get("daytrade") or 0) >= 35:
            checks.append(["warn", f"當沖比 {ch['daytrade']}% 偏高"])
        return {"strength": None, "hype": 0, "hype_lv": "低", "verdict": t, "vc": "", "checks": checks}
    st, hy, checks = 0, 0, []
    ok = lambda t: checks.append(["ok", t])
    bad = lambda t: checks.append(["bad", t])
    warn = lambda t: checks.append(["warn", t])
    m = f.get("mrev") or {}
    eps = f.get("eps_cum")
    # ---- 實力 ----
    if eps is not None:
        if eps > 0: st += 15; ok(f"有獲利：今年累計 EPS {eps:.2f} 元")
        else: bad(f"虧損中：今年累計 EPS {eps:.2f} 元")
    else:
        warn("查無本年度 EPS 資料")
    if f.get("op_margin") is not None:
        if f["op_margin"] >= 10: st += 10; ok(f"本業賺錢：營業利益率 {f['op_margin']}%")
        elif f["op_margin"] < 0: bad(f"本業虧損：營業利益率 {f['op_margin']}%")
    g = m.get("cum_yoy")
    if g is not None:
        if g >= 10: st += 15; ok(f"營收成長：今年累計年增 {g:.1f}%")
        elif g >= 0: st += 8; ok(f"營收持平小增：累計年增 {g:.1f}%")
        else: bad(f"營收衰退：累計年減 {abs(g):.1f}%")
    pe, ip = f.get("pe"), f.get("ind_pe")
    if not pe and f.get("eps_base") and f["eps_base"] > 0:
        pe = a["close"] / f["eps_base"]
    if pe and ip:
        if pe <= ip * 1.2: st += 10; ok(f"評價合理：本益比 {pe:.1f} 倍（同業 {ip:.1f}）")
        elif pe <= ip * 2: warn(f"評價偏高：本益比 {pe:.1f} 倍（同業 {ip:.1f}）")
        elif pe > ip * 2: bad(f"評價過高：本益比 {pe:.1f} 倍，是同業 {ip:.1f} 倍的 {pe / ip:.1f} 倍")
    d = f.get("div") or {}
    if d.get("cash"): st += 10; ok(f"有配息：現金股利 {d['cash']:.2f} 元")
    mc = ch.get("mcap")
    if mc is not None:
        if mc >= 100: st += 10; ok(f"市值 {mc:,.0f} 億，大型股不易被炒作")
        elif mc >= 30: st += 5
        else: warn(f"市值僅 {mc:,.1f} 億，小型股股價較易被拉抬")
    inst = a["f10"] + a["t10"]
    if inst > 0: st += 10; ok(f"法人站買方：外資+投信 10 日買超 {inst:,} 張")
    if ch.get("big1000") is not None:
        if ch["big1000"] >= 50: st += 10; ok(f"籌碼集中：千張大戶持股 {ch['big1000']}%")
        elif ch["big1000"] < 20: warn(f"籌碼分散：千張大戶僅持股 {ch['big1000']}%")
    fh = fin_health(a["code"], a)
    pat = price_patterns(a["code"], a)
    is_fin = (f.get("ind") or "").startswith("金融")
    if fh.get("gm") is not None and fh["gm"] >= 30: st += 5; ok(f"毛利率 {fh['gm']}%，產品有競爭力")
    if fh.get("roe") is not None:
        if fh["roe"] >= 15: st += 8; ok(f"ROE {fh['roe']}%，股東權益報酬率高")
        elif fh["roe"] < 0: bad(f"ROE {fh['roe']}%，侵蝕股東權益")
    if fh.get("debt") is not None and not is_fin:
        if fh["debt"] <= 50: st += 5; ok(f"負債比 {fh['debt']}%，財務穩健")
        elif fh["debt"] >= 70: bad(f"負債比 {fh['debt']}% 偏高")
    if (fh.get("foreign") or 0) >= 30: st += 5; ok(f"外資持股 {fh['foreign']}%，國際法人認同")
    if fh.get("dir_hold") is not None and fh["dir_hold"] >= 20 and (fh.get("dir_pledge") or 0) < 10:
        st += 5; ok(f"董監持股 {fh['dir_hold']}% 且幾乎未質押，經營層與股東利益一致")
    if fh.get("treasury") or any("買回" in m[1] for m in fh.get("mat", [])): ok("公司買回庫藏股，護盤意願強")
    for t, txt in pat["signals"]:
        if t == "good": ok(txt)
    # ---- 炒作警訊 ----
    pl = fh.get("dir_pledge") or 0
    if pl >= 50: hy += 20; bad(f"董監持股質押 {pl}%，有斷頭賣壓或護盤炒作疑慮")
    elif pl >= 30: hy += 10; warn(f"董監持股質押 {pl}% 偏高")
    if fh.get("dir_hold") is not None and fh["dir_hold"] < 10 and (ch.get("mcap") or 0) < 50:
        hy += 5; warn(f"董監持股僅 {fh['dir_hold']}%，經營權不穩、股價易受外力影響")
    if fh.get("ins"):
        tot = sum(x[3] for x in fh["ins"])
        hy += 10; warn(f"內部人近期申報轉讓（賣出）持股共 {tot:,} 張")
    if fh.get("viol"): hy += 10; bad("公司曾因重大訊息申報違規被裁罰")
    if any(k in m[1] for m in fh.get("mat", []) for k in ("現金增資", "私募", "可轉換公司債")):
        hy += 8; warn("近期公告現金增資 / 私募 / 可轉債，留意股本稀釋與拉抬籌資")
    if (fh.get("sbl_pct") or 0) >= 3: warn(f"借券賣出餘額占股本 {fh['sbl_pct']}%，空方壓力大")
    badp = [txt for t, txt in pat["signals"] if t != "good"]
    hy += min(20, 8 * len(badp))
    for txt in badp: (bad if "出貨" in txt or "漲停" in txt else warn)(txt)
    flags = ch.get("flags") or []
    kinds = {k for k, _ in flags}
    if "處置" in kinds: hy += 35; bad("目前為處置股（交易所認定交易異常，限制撮合）")
    elif "近期處置" in kinds: hy += 20; bad("近期曾被列為處置股")
    if kinds & {"注意", "注意累計"}: hy += 20; bad("被交易所列為注意股（漲幅或週轉率異常）")
    if ch.get("tv"): hy += 30; bad("被列入「投資理財節目異常推介個股」")
    r20 = a.get("ret20")
    if r20 is not None:
        if r20 >= 40: hy += 20; bad(f"20 日內飆漲 {r20:.0f}%")
        elif r20 >= 25: hy += 10; warn(f"20 日內大漲 {r20:.0f}%")
        if r20 >= 25 and ((g is not None and g < 0) or (eps is not None and eps <= 0)):
            hy += 20; bad("股價大漲但營收衰退或虧損，漲勢缺乏基本面支撐")
    vr = a["vol"] / a["vma20"] if a.get("vma20") else 0
    if vr >= 5: hy += 10; warn(f"成交量暴增至月均量 {vr:.1f} 倍")
    dtr = ch.get("daytrade")
    if dtr is not None:
        if dtr >= 50: hy += 15; bad(f"當沖比 {dtr}%，短線投機資金主導")
        elif dtr >= 35: hy += 8; warn(f"當沖比 {dtr}% 偏高")
    to = ch.get("turnover")
    if to is not None and to >= 10: hy += 10; warn(f"週轉率 {to}%，籌碼換手劇烈")
    if ch.get("margin_chg") and a["chg_pct"] > 0 and ch["margin_chg"] > 0 and inst < 0:
        hy += 10; warn(f"融資增加 {ch['margin_chg']:,.0f} 張但法人賣超，散戶追價")
    if ch.get("margin_use") and ch["margin_use"] >= 30: hy += 8; warn(f"融資使用率 {ch['margin_use']}% 偏高")
    if mc is not None and mc < 30 and r20 is not None and r20 >= 25: hy += 10
    if not pe and r20 is not None and r20 >= 25: hy += 10
    thm = themes_for(a["code"])
    if thm and st < 40: hy += 10; warn(f"新聞題材（{'、'.join(thm)}）帶動，但基本面偏弱")
    st, hy = min(st, 100), min(hy, 100)
    if st >= 75 and hy < 35: v, vc = "實力股", "ok"
    elif st >= 75: v, vc = "有實力但短線過熱", "warn"
    elif hy >= 50: v, vc = "疑似炒作", "bad"
    elif st < 35 and hy < 35: v, vc = "體質偏弱", "weak"
    elif hy >= 35: v, vc = "題材投機", "warn"
    else: v, vc = "中性觀察", ""
    hl = "高" if hy >= 50 else "中" if hy >= 25 else "低"
    return {"strength": st, "hype": hy, "hype_lv": hl, "verdict": v, "vc": vc, "checks": checks}


# ---------------------------------------------------------------- 當沖
DTLIST = {}    # code -> "" (可雙向當沖) / "Y" (暫停先賣後買)


def load_dtlist(d):
    c = load_cache("dtl", d)
    if c:
        return c
    out = {}
    for r in fetch_list("https://openapi.twse.com.tw/v1/exchangeReport/TWTB4U"):
        out[(r.get("Code") or "").strip()] = (r.get("Suspension") or "").strip()
    for r in fetch_list("https://www.tpex.org.tw/openapi/v1/tpex_securities"):
        out[(r.get("證券代號") or "").strip()] = (r.get("暫停現股賣出後現款買進當沖註記") or "").strip()
    out = {k: v for k, v in out.items() if k}
    if out:
        save_cache("dtl", d, out)
    return out


# ---------------------------------------------------------------- 配息頻率 / 值不值得買
DIVH = {}      # code -> [[除息日 YYYY-MM-DD, 現金股利, 除息前收盤, 權/息]]
FREQ_N = {"月配": 12, "雙月配": 6, "季配": 4, "半年配": 2, "年配": 1}


def load_divhist(d):
    """近 15 個月的除權息紀錄（上市 TWT49U、上櫃 exDailyQ），用來判斷配息頻率與填息"""
    c = load_cache("dvh", d)
    if c:
        return c
    out = {}
    st = d - timedelta(days=450)
    try:
        js = http_get(f"https://www.twse.com.tw/rwd/zh/exRight/TWT49U?startDate={st:%Y%m%d}&endDate={d:%Y%m%d}&response=json", timeout=60)
        for r in js.get("data") or []:
            m = re.match(r"(\d+)年(\d+)月(\d+)日", r[0])
            if not m:
                continue
            ds = f"{int(m[1]) + 1911}-{m[2]}-{m[3]}"
            cash = num(r[5]) if "息" in r[6] else 0
            out.setdefault(r[1].strip(), []).append([ds, round(cash or 0, 4), num(r[3]), r[6]])
    except Exception as e:
        print("  ! 上市除權息紀錄失敗", e)
    try:
        body = urllib.parse.urlencode({"startDate": f"{st:%Y/%m/%d}", "endDate": f"{d:%Y/%m/%d}", "response": "json"}).encode()
        req = urllib.request.Request("https://www.tpex.org.tw/www/zh-tw/bulletin/exDailyQ", data=body, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=60, context=SSL_CTX) as r:
            js = json.loads(r.read().decode("utf-8", "replace"))
        for r in (js.get("tables") or [{}])[0].get("data") or []:
            y, mo, da = r[0].split("/")
            out.setdefault(r[1].strip(), []).append([f"{int(y) + 1911}-{mo}-{da}", round(num(r[13]) or 0, 4), num(r[3]), r[8].replace("除", "")])
    except Exception as e:
        print("  ! 上櫃除權息紀錄失敗", e)
    for v in out.values():
        v.sort()
    if len(out) > 300:
        save_cache("dvh", d, out)
    return out


def div_analysis(a):
    """配息頻率、年化殖利率、填息狀況，並判斷「為了配息買值不值得」"""
    code, c = a["code"], a["close"]
    if is_etf(code) and code[-1] in "LR":
        return {"freq": "不配息", "verdict": "不適合領息", "vc": "bad", "score": 0, "events": [],
                "why": [["bad", "槓桿 / 反向型 ETF 不以配息為目的，長期持有會耗損，只適合短線"]]}
    today = datetime.strptime(a["date"], "%Y-%m-%d").date()
    ev = [e for e in DIVH.get(code, []) if e[1] > 0 and (today - datetime.strptime(e[0], "%Y-%m-%d").date()).days <= 400]
    ex = (PROFILE.get(code) or {}).get("ex") or {}
    nxt = None
    if ex.get("date") and ex["date"].replace("/", "-") > a["date"] and "權" not in (ex.get("type") or "")[-1:]:
        nxt = {"date": ex["date"].replace("/", "-"), "cash": ex.get("cash")}
    if not ev:
        return None if not nxt else {"freq": "新配息", "events": [], "next": nxt, "verdict": "資料不足", "vc": "", "score": None, "why": []}
    ds = [datetime.strptime(e[0], "%Y-%m-%d").date() for e in ev]
    if len(ev) >= 2:
        gaps = sorted((ds[i + 1] - ds[i]).days for i in range(len(ds) - 1))
        g = gaps[len(gaps) // 2]
        freq = "月配" if g <= 40 else "雙月配" if g <= 75 else "季配" if g <= 125 else "半年配" if g <= 240 else "年配"
    else:
        freq = "年配"
    n = FREQ_N[freq]
    recent = ev[-n:]
    last = ev[-1][1]
    est = round(sum(e[1] for e in recent) / len(recent) * n, 4)
    ttm = round(sum(e[1] for e in ev if (today - datetime.strptime(e[0], "%Y-%m-%d").date()).days <= 365), 4)
    yld = round(est / c * 100, 2) if c else None
    # 填息：除息後股價回到除息前收盤價
    s = HIST.get(code) or {}
    fills = []
    for e in ev[-4:]:
        pre = e[2]
        if not pre:
            continue
        dl = s.get("dates") or []
        idx = [i for i, x in enumerate(dl) if x >= e[0]] if dl and e[0] >= dl[0] else []
        days = None
        for k, i in enumerate(idx):
            if s["h"][i] >= pre:
                days = k + 1; break
        fills.append({"date": e[0], "cash": e[1], "pre": pre, "filled": days is not None or c >= pre, "days": days})
    fr = sum(1 for x in fills if x["filled"]) / len(fills) if fills else None
    sc, why = 0, []
    if yld is None:
        pass
    elif yld >= 8:
        sc += 30; why.append(["ok", f"年化殖利率 {yld}%，非常高（但超過 10% 要留意是否用本金配息、能否持續）" if yld > 10 else f"年化殖利率 {yld}%，很高"])
    elif yld >= 6:
        sc += 25; why.append(["ok", f"年化殖利率 {yld}%，高於定存很多"])
    elif yld >= 4:
        sc += 15; why.append(["ok", f"年化殖利率 {yld}%，不錯"])
    elif yld >= 2.5:
        sc += 5; why.append(["warn", f"年化殖利率 {yld}%，普通，買它主要是看成長而不是配息"])
    else:
        sc -= 5; why.append(["bad", f"年化殖利率只有 {yld}%，單純領息不划算"])
    if fr is not None:
        if fr >= 0.75:
            sc += 25; why.append(["ok", f"最近 {len(fills)} 次配息有 {sum(x['filled'] for x in fills)} 次已填息，領了股息價格也回來了"])
        elif fr >= 0.5:
            sc += 10; why.append(["warn", f"最近 {len(fills)} 次配息有 {sum(x['filled'] for x in fills)} 次填息，填息速度普通"])
        else:
            sc -= 15; why.append(["bad", f"最近 {len(fills)} 次配息只有 {sum(x['filled'] for x in fills)} 次填息，容易「賺了股息、賠了價差」"])
    if len(ev) >= 3:
        prev = [e[1] for e in ev[-n - 1:-1]] or [e[1] for e in ev[:-1]]
        avg = sum(prev) / len(prev)
        if last >= avg * 0.95:
            sc += 10; why.append(["ok", f"最近一次配 {last:g} 元，沒有縮水" + ("，還有變多" if last > avg * 1.05 else "")])
        elif last < avg * 0.8:
            sc -= 10; why.append(["bad", f"最近一次配 {last:g} 元，比之前平均 {avg:.3g} 元少了 {round((1 - last / avg) * 100)}%"])
    if a.get("ma60"):
        b = (c / a["ma60"] - 1) * 100
        if b >= 0:
            sc += 10; why.append(["ok", "股價在季線之上，趨勢穩定"])
        elif b < -5:
            sc -= 10; why.append(["warn", f"股價低於季線 {abs(round(b))}%，價格還在跌，可分批慢慢買"])
    if not is_nonstock(code):
        f = fundamentals(a)
        if f.get("payout") and f["payout"] > 100:
            sc -= 15; why.append(["bad", f"配發率 {f['payout']:.0f}%，配的比賺的多，之後股息可能減少"])
        elif f.get("eps_ttm") is not None and f["eps_ttm"] <= 0:
            sc -= 15; why.append(["bad", "近四季虧損，股息不容易維持"])
        v = sv_of(a)["verdict"]
        if v in ("疑似炒作", "題材投機"):
            sc -= 15; why.append(["bad", f"鑑定為「{v}」，不適合存股"])
    elif code.endswith("B"):
        why.append(["warn", "債券型 ETF：利率下降時價格會漲、利率上升時會跌"])
    if nxt:
        why.append(["warn", f"下次除息 {nxt['date']}" + (f"，每單位 {nxt['cash']:g} 元" if nxt.get("cash") else "（金額尚未公告）") +
                    "；單次領超過 2 萬元要扣 2.11% 健保補充保費，也要併入所得稅"])
    verdict, vc = ("值得買", "ok") if sc >= 55 else ("可以考慮", "ok") if sc >= 35 else ("普通", "warn") if sc >= 15 else ("不建議只為配息買", "bad")
    months = sorted({int(e[0][5:7]) for e in ev})
    return {"freq": freq, "months": months, "last": last, "est": est, "ttm": ttm, "yield": yld, "fills": fills,
            "fill_rate": round(fr * 100) if fr is not None else None, "next": nxt, "score": sc, "verdict": verdict, "vc": vc,
            "why": why, "events": ev[-12:]}


def div_list(latest):
    """配息股清單（依頻率分類），每列：代號 名稱 種類 頻率 除息月份 最近配 年化殖利率 填息率 分數 判斷 下次除息 收盤 漲跌"""
    out = []
    for a in latest:
        if a["vol"] < 20:
            continue
        d = div_analysis(a)
        if not d or d["freq"] not in FREQ_N:
            continue
        out.append([a["code"], a["name"], sec_type(a["code"]), d["freq"], d["months"], d["last"], d["yield"], d["fill_rate"],
                    d["score"], d["verdict"], (d["next"] or {}).get("date"), a["close"], a["chg_pct"]])
    out.sort(key=lambda r: -(r[8] or 0))
    return out


def etf_list(latest):
    """ETF 買賣建議：成交量足夠的 ETF，附進出場價與配息判斷"""
    out = []
    for a in latest:
        if sec_type(a["code"]) != "ETF" or (a["vma20"] or 0) < 300 or a["days"] < 30:
            continue
        p = generic_plan(a)
        d = div_analysis(a) or {}
        lev = a["code"][-1] in "LR"
        kind = "槓桿/反向" if lev else "債券" if a["code"].endswith("B") else "股票型"
        if p["trend"] == "多頭" and (a["rsi"] or 50) < 75:
            act, ac = "可分批買進", "up"
        elif p["trend"] == "多頭":
            act, ac = "偏多但過熱，等拉回", ""
        elif p["trend"] == "空頭":
            act, ac = ("先觀望（短線偏弱）" if lev else "等站回月線再買；存股可小量分批"), "down"
        else:
            act, ac = "盤整，靠近進場區再買", ""
        out.append({"code": a["code"], "name": a["name"], "kind": kind, "close": a["close"], "chg_pct": a["chg_pct"], "vol": a["vol"],
                    "ret20": a.get("ret20"), "plan": p, "act": act, "ac": ac, "freq": d.get("freq"), "yield": d.get("yield"),
                    "dv": d.get("verdict"), "dvc": d.get("vc"), "value": round(a["vol"] * a["close"] / 1e5, 1)})
    out.sort(key=lambda r: -r["value"])
    return out[:150]


# ---------------------------------------------------------------- 無漲跌幅限制
NOLIM = {}     # code -> {"name", "up", "ref"}；漲停價 9999.95 / 9995 代表沒有漲跌幅限制


def load_nolimit(d):
    c = load_cache("nlm", d)
    if c:
        return c
    out = {}
    for r in fetch_list("https://openapi.twse.com.tw/v1/exchangeReport/TWT84U"):
        code, up, ref = (r.get("Code") or "").strip(), num(r.get("TodayLimitUp")), num(r.get("TodayOpeningRefPrice"))
        if is_stock_code(code) and up and ref and up / ref > 1.25:
            out[code] = {"name": r.get("Name", "").strip(), "up": up, "ref": ref}
    for r in fetch_list("https://www.tpex.org.tw/openapi/v1/tpex_mainboard_daily_close_quotes"):
        code, up, ref = (r.get("SecuritiesCompanyCode") or "").strip(), num(r.get("NextLimitUp")), num(r.get("NextReferencePrice") or r.get("Close"))
        if is_stock_code(code) and up and ref and up / ref > 1.25:
            out[code] = {"name": r.get("CompanyName", "").strip(), "up": up, "ref": ref}
    if out:
        save_cache("nlm", d, out)
    return out


def nolimit_reason(code, days):
    st = sec_type(code)
    if st == "股票" and days is not None and days <= 5:
        return "新股", "剛上市 / 上櫃，前 5 個交易日沒有漲跌幅限制"
    if st == "ETF" and code.endswith("B"):
        return "債券ETF", "債券型 ETF 沒有漲跌幅限制"
    if st in ("ETF", "ETN"):
        return "海外" + st, "追蹤國外市場或商品，沒有漲跌幅限制，價格跟著國外走"
    return "其他", "暫停交易後恢復、或其他原因，暫時沒有漲跌幅限制"


def new_stock_plan(code, n):
    """新股（歷史很短）：用上市以來的高低點判斷能不能進場"""
    s = HIST[code]
    c, lo, hi = s["c"][-1], min(s["l"]), max(s["h"])
    first = s["o"][0]
    vol_down = len(s["v"]) >= 2 and s["v"][-1] < s["v"][-2] * 0.7
    chg = (c / s["c"][-2] - 1) * 100 if len(s["c"]) >= 2 else (c / first - 1) * 100
    gain = (c / first - 1) * 100
    stop = rnd(max(lo * 0.97, c * 0.88), "down")
    t1, t2 = rnd(c * 1.1, "up"), rnd(max(hi, c * 1.2), "up")
    left = max(5 - n, 0)
    if gain > 60:
        act, ac = "漲幅已大，不建議進場", "down"
    elif c < first * 0.9 and chg < 0:
        act, ac = "破底下跌中，先觀望", "down"
    elif vol_down and c >= lo * 1.03 and chg > -3:
        act, ac = "量縮止穩，可小量短打", "up"
    else:
        act, ac = "波動太大，等量縮止穩再看", ""
    return {"act": act, "ac": ac, "entry": f"回到 {rnd(max(lo, c * 0.95), 'down')} 附近、成交量變小且不再破底時，少量買進",
            "stop": stop, "t1": t1, "t2": t2, "first": first, "lo": lo, "hi": hi, "gain": round(gain, 1), "days": n, "left": left,
            "exit": (f"還剩 {left} 天就恢復漲跌幅限制，" if left else "") + "到目標一先賣一半；碰停損立刻賣；出現爆量長黑（大量下跌）也要先出場",
            "chg": round(chg, 2), "close": c}


def nolimit_list(all_a, last_date):
    ds = last_date.strftime("%Y-%m-%d")
    first_day = min((h["dates"][0] for h in HIST.values() if h["dates"]), default=None)
    out = []
    for code, v in NOLIM.items():
        s = HIST.get(code)
        if not s and sec_type(code) == "股票":    # 下一個交易日才第一天上市
            out.append({"code": code, "name": v["name"], "kind": "新股", "why": "下一個交易日第一天掛牌，前 5 天沒有漲跌幅限制", "close": v["ref"],
                        "vol": 0, "chg_pct": None, "upcoming": True, "in_detail": False})
            continue
        if not s or s["dates"][-1] != ds:
            continue
        n = len(s["dates"]) if first_day and s["dates"][0] > first_day else None
        kind, why = nolimit_reason(code, n)
        o = {"code": code, "name": s["name"], "market": s["market"], "kind": kind, "why": why, "close": s["c"][-1], "vol": s["v"][-1],
             "up": v["up"], "in_detail": code in all_a and len(s["c"]) >= 30}
        a = all_a.get(code)
        if kind == "新股" or not a:
            if len(s["c"]) < 1:
                continue
            o["np"] = new_stock_plan(code, len(s["c"]))
            o["chg_pct"] = o["np"]["chg"]
        else:
            if (a["vma20"] or 0) < 50 and kind != "其他":
                continue
            p = generic_plan(a)
            o.update(chg_pct=a["chg_pct"], plan=p, ret20=a.get("ret20"))
            if p["trend"] == "多頭" and (a["rsi"] or 50) < 75:
                o["act"], o["ac"] = "可分批買進", "up"
            elif p["trend"] == "多頭":
                o["act"], o["ac"] = "偏多但過熱，等拉回", ""
            elif p["trend"] == "空頭":
                o["act"], o["ac"] = "趨勢偏弱，先觀望", "down"
            else:
                o["act"], o["ac"] = "盤整，靠近進場區再買", ""
            o["exit"] = ("國外市場晚上大跌，隔天早上可能直接跳空，" if kind.startswith("海外") else "") + \
                        f"到目標一 {p['t1']} 先賣一半、目標二 {p['t2']} 全賣；收盤跌破停損 {p['stop']} 就出場"
        out.append(o)
    order = {"新股": 0, "其他": 1, "海外ETF": 2, "海外ETN": 3, "債券ETF": 4}
    out.sort(key=lambda o: (order.get(o["kind"], 9), -(o["vol"] * o["close"])))
    return out


def daytrade_info(a):
    """可否當沖、昨日當沖比、今日樞紐價位（壓力 / 支撐）"""
    code = a["code"]
    s = HIST[code]
    h, l, c = s["h"][-1], s["l"][-1], s["c"][-1]
    pp = (h + l + c) / 3
    flags = {k for k, _ in RISK.get("flags", {}).get(code, [])}
    dtv = RISK.get("dt", {}).get(code)
    o = {"ok": code in DTLIST and "處置" not in flags, "listed": code in DTLIST, "susp": DTLIST.get(code) == "Y", "dispose": "處置" in flags,
         "ratio": round(dtv / a["vol"] * 100, 1) if dtv is not None and a["vol"] else None,
         "atr_pct": round(a["atr"] / c * 100, 2) if c else None,
         "pp": rnd(pp), "r1": rnd(2 * pp - l), "s1": rnd(2 * pp - h), "r2": rnd(pp + (h - l)), "s2": rnd(pp - (h - l))}
    ma5, ma20 = a.get("ma5"), a.get("ma20")
    o["trend"] = "偏多" if ma5 and ma20 and c > ma5 > ma20 else "偏空" if ma5 and ma20 and c < ma5 < ma20 else "震盪"
    o["plan"] = daytrade_plan(o, a.get("atr") or (h - l))
    return o


def daytrade_plan(o, atr):
    """當沖進出場計畫：何時、多少價位進場，停損、停利與最晚出場時間"""
    if not o["ok"] or not o["pp"]:
        return None
    pad = max(atr * 0.3, tick(o["pp"]) * 2)
    pp, r1, r2, s1, s2 = o["pp"], o["r1"], o["r2"], o["s1"], o["s2"]
    if o["trend"] == "偏空" and not o["susp"]:
        p = {"side": "空", "title": "先賣後買（做空）", "entry": rnd(pp, "down"), "stop": rnd(pp + pad, "up"), "t1": s1, "t2": s2,
             "when": "9:15 以後，股價跌破 PP 而且跌破「開盤前 15 分鐘的最低價」時，先賣出",
             "skip": "如果 9:15 後股價一直站在 PP 之上，今天不要做空"}
    elif o["trend"] == "偏多":
        p = {"side": "多", "title": "先買後賣（做多）", "entry": rnd(pp, "up"), "stop": rnd(pp - pad, "down"), "t1": r1, "t2": r2,
             "when": "9:15 以後，股價站穩 PP 之上而且突破「開盤前 15 分鐘的最高價」時，買進",
             "skip": "如果開盤就跌破 PP、或一開盤就大漲超過 R1，今天不要追"}
    else:
        p = {"side": "多", "title": "低接（區間來回）", "entry": rnd(s1, "up"), "stop": rnd(s1 - pad, "down"), "t1": pp, "t2": r1,
             "when": "9:30 以後，股價回到 S1 附近、而且連續幾分鐘不再破底（止跌）時，買進",
             "skip": "如果股價跌破停損價就不要接；沒有回到 S1 就不要追高"}
    risk = abs(p["entry"] - p["stop"])
    p["rr"] = round(abs(p["t1"] - p["entry"]) / risk, 1) if risk else None
    p["exit"] = "到第一目標先賣一半，剩下的到第二目標或 13:20 前全部出清；碰到停損價馬上出場，不要凹單"
    p["last"] = "13:20"
    return p


def daytrade_list(latest):
    """當沖參考名單：可當沖、成交量大、波動夠、非處置股"""
    rows = []
    for a in latest:
        if (a["vma20"] or 0) < 3000 or a["close"] < 10 or a["vol"] < 2000:
            continue
        d = daytrade_info(a)
        if not d["ok"] or (d["atr_pct"] or 0) < 2.5:
            continue
        score = (d["atr_pct"] or 0) * 10 + min(a["vol"] / a["vma20"], 4) * 8 + (d["ratio"] or 0) * 0.3
        rows.append((score, a, d))
    rows.sort(key=lambda x: -x[0])
    out = []
    for _, a, d in rows[:20]:
        out.append({"code": a["code"], "name": a["name"], "market": a["market"], "close": a["close"], "chg_pct": a["chg_pct"], "vol": a["vol"],
                    "etf": is_nonstock(a["code"]), **d})
    return out


# ---------------------------------------------------------------- 財報、董監、外資持股、重大訊息
EXTRA = {}     # 最新: 財報 / 董監質押 / 外資持股 / 借券 / 大股東 / 違規
TAIEX_RET20 = None
DATES = []     # 最近交易日 (K 線用)


def pick(r, *keys):
    for k in keys:
        if k in r and str(r[k]).strip() not in ("", "-"):
            return num(r[k])
    return None


def load_extra(d):
    c = load_cache("extra", d)
    if c:
        return c
    tw, tp = "https://openapi.twse.com.tw/v1/opendata/", "https://www.tpex.org.tw/openapi/v1/mopsfin_"
    inc, bal, dirs, qf, sbl, bigh, viol, mat, ins = {}, {}, {}, {}, {}, {}, {}, {}, {}
    code_of = lambda r: (r.get("公司代號") or r.get("SecuritiesCompanyCode") or r.get("股票代號") or "").strip()
    for kind in ("ci", "mim", "basi", "bd", "fh", "ins"):
        for url in (f"{tw}t187ap06_L_{kind}", f"{tp}t187ap06_O_{kind}"):
            for r in fetch_list(url):
                code = code_of(r)
                if not is_stock_code(code):
                    continue
                inc[code] = {"rev": pick(r, "營業收入", "收益", "收入", "淨收益", "利息淨收益"),
                             "gross": pick(r, "營業毛利（毛損）淨額", "營業毛利（毛損）"),
                             "op": pick(r, "營業利益（損失）", "營業利益"),
                             "ni": pick(r, "淨利（淨損）歸屬於母公司業主", "淨利（損）歸屬於母公司業主", "本期淨利（淨損）", "本期稅後淨利（淨損）"),
                             "q": int(num(r.get("季別") or r.get("Season")) or 0)}
        for url in (f"{tw}t187ap07_L_{kind}", f"{tp}t187ap07_O_{kind}"):
            for r in fetch_list(url):
                code = code_of(r)
                if not is_stock_code(code):
                    continue
                bal[code] = {"assets": pick(r, "資產總計", "資產總額"), "liab": pick(r, "負債總計", "負債總額"),
                             "ca": pick(r, "流動資產"), "cl": pick(r, "流動負債"),
                             "eq": pick(r, "歸屬於母公司業主之權益合計", "權益總計", "權益總額"),
                             "bvps": pick(r, "每股參考淨值"), "treasury": pick(r, "庫藏股票")}
    # 董監持股與質押
    for url in (f"{tw}t187ap11_L", f"{tp}t187ap11_O"):
        for r in fetch_list(url):
            code = code_of(r)
            title = r.get("職稱", "")
            if not is_stock_code(code) or not ("董事" in title or "監察人" in title):
                continue
            o = dirs.setdefault(code, [0, 0])
            o[0] += num(r.get("目前持股")) or 0
            o[1] += num(r.get("設質股數")) or 0
    # 外資持股比例
    try:
        js = http_get(f"https://www.twse.com.tw/rwd/zh/fund/MI_QFIIS?date={d:%Y%m%d}&selectType=ALLBUT0999&response=json")
        for row in js.get("data", []):
            if is_stock_code(row[0].strip()):
                qf[row[0].strip()] = num(row[7])
    except Exception as e:
        print("  ! 外資持股資料失敗", e)
    for r in fetch_list("https://www.tpex.org.tw/openapi/v1/tpex_3insti_qfii"):
        code = code_of(r)
        if is_stock_code(code):
            qf[code] = num((r.get("PercentageOfSharesOC/FMIHeld") or "").replace("%", ""))
    # 借券賣出餘額 (張)
    try:
        js = http_get(f"https://www.twse.com.tw/rwd/zh/marginTrading/TWT93U?date={d:%Y%m%d}&response=json")
        for row in js.get("data", []):
            if is_stock_code(row[0].strip()):
                sbl[row[0].strip()] = round((num(row[12]) or 0) / 1000)
    except Exception as e:
        print("  ! 借券資料失敗", e)
    for r in fetch_list("https://www.tpex.org.tw/openapi/v1/tpex_margin_sbl"):
        code = code_of(r)
        if is_stock_code(code):
            sbl[code] = round((num(r.get("SecuritiesBorrowingBalanceOfTheMarketDay")) or 0) / 1000)
    # 大股東、違規、重大訊息、內部人轉讓
    for url in (f"{tw}t187ap02_L", f"{tp}t187ap02_O"):
        for r in fetch_list(url):
            code = code_of(r)
            if is_stock_code(code):
                bigh.setdefault(code, []).append((r.get("大股東名稱") or "").strip())
    for url in (f"{tw}t187ap23_L", f"{tp}t187ap23_O"):
        for r in fetch_list(url):
            code = code_of(r)
            if is_stock_code(code):
                viol.setdefault(code, []).append([roc_date(r.get("發函日期")), (r.get("違規事由") or "").replace("\r", "").replace("\n", "")[:160],
                                                  r.get("裁罰金額(萬)")])
    for url in (f"{tw}t187ap04_L", f"{tp}t187ap04_O"):
        for r in fetch_list(url):
            code = code_of(r)
            if is_stock_code(code):
                subj = (r.get("主旨 ") or r.get("主旨") or "").replace("\r", "").replace("\n", "")
                mat.setdefault(code, []).append([roc_date(r.get("發言日期")), subj[:200]])
    for url in (f"{tw}t187ap12_L", f"{tp}t187ap12_O"):
        for r in fetch_list(url):
            code = code_of(r)
            if is_stock_code(code):
                ins.setdefault(code, []).append([roc_date(r.get("出表日期") or r.get("Date")), (r.get("申報人身分") or "").strip(),
                                                 (r.get("姓名") or "").strip(),
                                                 round((num(r.get("預定轉讓總股數-自有持股")) or 0) / 1000),
                                                 (r.get("預定轉讓方式及股數-轉讓方式") or "").strip()])
    c = {"inc": inc, "bal": bal, "dirs": dirs, "qf": qf, "sbl": sbl, "bigh": bigh, "viol": viol, "mat": mat, "ins": ins}
    if inc and bal:
        save_cache("extra", d, c)
    return c


def merge_events(prev, key):
    """重大訊息、內部人轉讓每天只公布當日，累積起來保留最近幾筆"""
    out = {c: [list(x) for x in v] for c, v in (prev or {}).get(key, {}).items()}
    for fn in sorted(os.listdir(DATA_DIR)):
        if fn.endswith("_extra.json"):
            try:
                with open(os.path.join(DATA_DIR, fn), encoding="utf-8") as fh:
                    c = json.load(fh)
            except Exception:
                continue
            for code, rows in c.get(key, {}).items():
                lst = out.setdefault(code, [])
                for r in rows:
                    if r not in lst:
                        lst.append(r)
    return {c: sorted(v, key=lambda x: x[0], reverse=True)[:12] for c, v in out.items()}


def fin_health(code, a):
    """財報體質: 毛利率、營益率、ROE、負債比、流動比、董監持股與質押、外資持股、借券"""
    p = PROFILE.get(code, {})
    inc, bal = EXTRA.get("inc", {}).get(code), EXTRA.get("bal", {}).get(code)
    o = {}
    if inc and inc.get("rev"):
        if inc.get("gross") is not None:
            o["gm"] = round(inc["gross"] / inc["rev"] * 100, 1)
        if inc.get("op") is not None:
            o["om"] = round(inc["op"] / inc["rev"] * 100, 1)
    if bal:
        if bal.get("assets") and bal.get("liab") is not None:
            o["debt"] = round(bal["liab"] / bal["assets"] * 100, 1)
        if bal.get("ca") and bal.get("cl"):
            o["cur"] = round(bal["ca"] / bal["cl"] * 100, 0)
        o["bvps"] = bal.get("bvps")
        if bal.get("treasury"):
            o["treasury"] = True
        if inc and inc.get("ni") is not None and bal.get("eq") and inc.get("q"):
            o["roe"] = round(inc["ni"] * 4 / inc["q"] / bal["eq"] * 100, 1)
        if inc and inc.get("ni") is not None and bal.get("assets") and inc.get("q"):
            o["roa"] = round(inc["ni"] * 4 / inc["q"] / bal["assets"] * 100, 1)
    dr = EXTRA.get("dirs", {}).get(code)
    if dr and p.get("shares"):
        o["dir_hold"] = round(dr[0] / p["shares"] * 100, 1)
        o["dir_pledge"] = round(dr[1] / dr[0] * 100, 1) if dr[0] else 0
    if EXTRA.get("qf", {}).get(code) is not None:
        o["foreign"] = EXTRA["qf"][code]
    if EXTRA.get("sbl", {}).get(code) is not None:
        o["sbl"] = EXTRA["sbl"][code]
        if p.get("shares"):
            o["sbl_pct"] = round(o["sbl"] * 1000 / p["shares"] * 100, 2)
    o["bigh"] = EXTRA.get("bigh", {}).get(code, [])[:6]
    o["viol"] = EXTRA.get("viol", {}).get(code, [])
    o["mat"] = HIST2.get("mat", {}).get(code, [])[:8]
    o["ins"] = HIST2.get("ins", {}).get(code, [])[:8]
    return o


def price_patterns(code, a):
    """量價型態: 主力出貨 / 進貨 / 連續漲停 / 跳空"""
    s = HIST[code]
    o, h, l, c, v = s["o"], s["h"], s["l"], s["c"], s["v"]
    n = len(c)
    sig = []    # [類型 good/bad/warn, 說明]
    vma = sum(v[-21:-1]) / 20 if n > 21 else None
    for i in range(max(1, n - 5), n):
        rng = h[i] - l[i]
        if not rng or not vma:
            continue
        upper = h[i] - max(o[i], c[i])
        body = abs(c[i] - o[i])
        hi20 = max(h[max(0, i - 20):i + 1])
        ago = n - 1 - i
        when = "今日" if ago == 0 else f"{ago} 日前"
        if v[i] > vma * 2 and upper > rng * 0.5 and h[i] >= hi20 * 0.97:
            sig.append(["bad", f"{when}高檔爆量長上影線，疑似主力逢高出貨"])
        elif v[i] > vma * 2 and c[i] < o[i] and body > rng * 0.6 and h[i] >= hi20 * 0.95:
            sig.append(["bad", f"{when}高檔爆量長黑 K，賣壓沉重"])
        elif v[i] > vma * 2 and c[i] > o[i] and body > rng * 0.6 and c[i] >= hi20 * 0.98:
            sig.append(["good", f"{when}帶量長紅突破，買盤積極"])
        lower = min(o[i], c[i]) - l[i]
        lo20 = min(l[max(0, i - 20):i + 1])
        if v[i] > vma * 1.5 and lower > rng * 0.5 and l[i] <= lo20 * 1.03:
            sig.append(["good", f"{when}低檔帶量長下影線，有買盤承接"])
    lim = sum(1 for i in range(max(1, n - 5), n) if c[i - 1] and c[i] / c[i - 1] - 1 >= 0.095)
    if lim >= 2:
        sig.append(["bad", f"近 5 日 {lim} 根漲停，短線追價風險高"])
    if n >= 6 and c[-1] > c[-6] * 1.05 and sum(v[-5:]) < sum(v[-10:-5]) * 0.7:
        sig.append(["warn", "價漲量縮，追價力道減弱（量價背離）"])
    if n >= 6 and c[-1] < c[-6] * 0.95 and sum(v[-5:]) > sum(v[-10:-5]) * 1.5:
        sig.append(["bad", "價跌量增，籌碼鬆動"])
    if n >= 2 and l[-1] > h[-2]:
        sig.append(["good", "今日跳空上漲，缺口未補"])
    elif n >= 2 and h[-1] < l[-2]:
        sig.append(["bad", "今日跳空下跌，留下缺口"])
    # 風險指標
    rets = [c[i] / c[i - 1] - 1 for i in range(max(1, n - 60), n) if c[i - 1]]
    vol = (sum(r * r for r in rets) / len(rets)) ** 0.5 * (250 ** 0.5) * 100 if rets else None
    peak, mdd = c[max(0, n - 60)], 0
    for x in c[max(0, n - 60):]:
        peak = max(peak, x)
        mdd = min(mdd, x / peak - 1)
    rs = round(a["ret20"] - TAIEX_RET20, 1) if a.get("ret20") is not None and TAIEX_RET20 is not None else None
    return {"signals": sig, "vol": round(vol, 1) if vol else None, "mdd": round(mdd * 100, 1), "rs": rs}


def grade(x):
    return "A" if x >= 80 else "B" if x >= 65 else "C" if x >= 50 else "D" if x >= 35 else "E"


def scorecard(a, f, fh, ch, sv, pat):
    """分析師評分卡: 8 個面向 0~100 分（ETF 只看技術面、籌碼、股利）"""
    if is_nonstock(a["code"]):
        clamp = lambda x: max(0, min(100, round(x)))
        inst = a["f10"] + a["t10"]
        tech = clamp(50 + (20 if a["close"] > a["ma20"] else -20) + (10 if a.get("ma60") and a["close"] > a["ma60"] else -10) + (pat.get("rs") or 0) * 0.8)
        chip = clamp(50 + (12 if inst > 0 else -12))
        d = (f.get("div") or {})
        items = [["技術面", tech, grade(tech), f"相對大盤 {pat['rs']:+.1f}%" if pat.get("rs") is not None else "趨勢判斷"],
                 ["籌碼", chip, grade(chip), f"法人 10 日 {inst:+,} 張"]]
        if d.get("ex"):
            items.append(["股利", 70, "B", f"即將{d['ex'].get('type', '除息')} {d['ex'].get('date', '')}"])
        tot = round(sum(x[1] for x in items) / len(items))
        return {"items": items, "total": tot, "grade": grade(tot)}
    m = f.get("mrev") or {}
    clamp = lambda x: max(0, min(100, round(x)))
    out = []
    g, y = m.get("cum_yoy"), m.get("yoy")
    if g is not None:
        out.append(["成長性", clamp(50 + g * 1.2 + (y or 0) * 0.3), f"累計營收年增 {g:.1f}%"])
    else:
        out.append(["成長性", None, "無營收資料"])
    gm, om, roe = fh.get("gm"), fh.get("om") if fh.get("om") is not None else f.get("op_margin"), fh.get("roe")
    if roe is not None or om is not None:
        sc = 40 + (roe or 0) * 2 + (om or 0) * 0.8 + ((gm or 0) - 20) * 0.3
        out.append(["獲利能力", clamp(sc), " / ".join(x for x in [f"ROE {roe}%" if roe is not None else "", f"營益率 {om}%" if om is not None else "",
                                                               f"毛利率 {gm}%" if gm is not None else ""] if x)])
    else:
        out.append(["獲利能力", None, "無財報資料"])
    debt, cur, pl = fh.get("debt"), fh.get("cur"), fh.get("dir_pledge")
    if debt is not None:
        is_fin = (f.get("ind") or "").startswith("金融")
        sc = 75 if is_fin else 100 - debt
        if cur is not None and not is_fin: sc += 10 if cur >= 150 else -10 if cur < 100 else 0
        if pl: sc -= pl * 0.5
        out.append(["財務體質", clamp(sc), f"負債比 {debt}%" + (f" / 流動比 {cur:.0f}%" if cur and not is_fin else "") + (f" / 董監質押 {pl}%" if pl else "")])
    else:
        out.append(["財務體質", None, "無財報資料"])
    pe, ip = f.get("pe"), f.get("ind_pe")
    if not pe and f.get("eps_base") and f["eps_base"] > 0:
        pe = a["close"] / f["eps_base"]
    if pe and ip:
        out.append(["評價", clamp(100 - (pe / ip - 0.6) * 60), f"本益比 {pe:.1f} / 同業 {ip:.1f}"])
    else:
        out.append(["評價", 15 if (f.get("eps_cum") or 0) < 0 else None, "虧損，無法評價" if (f.get("eps_cum") or 0) < 0 else "無本益比"])
    d = f.get("div") or {}
    if d.get("yield") is not None:
        out.append(["股利", clamp(d["yield"] * 15 + (10 if d.get("cash") else 0)), f"殖利率 {d['yield']}%"])
    else:
        out.append(["股利", 10, "近期未配息"])
    inst = a["f10"] + a["t10"]
    sc = 50 + (12 if inst > 0 else -12) + ((fh.get("foreign") or 0) - 20) * 0.5 + ((ch.get("big1000") or 50) - 50) * 0.4
    if ch.get("margin_chg_n") and ch["margin_chg_n"][1] > 0 and inst < 0: sc -= 10
    out.append(["籌碼", clamp(sc), f"法人 10 日 {inst:+,} 張" + (f" / 外資持股 {fh['foreign']}%" if fh.get("foreign") is not None else "")])
    sc = 50 + (20 if a["close"] > a["ma20"] else -20) + (10 if a.get("ma60") and a["close"] > a["ma60"] else -10) + (pat.get("rs") or 0) * 0.8
    sc += sum(6 if t == "good" else -8 for t, _ in pat["signals"])
    out.append(["技術面", clamp(sc), f"相對大盤 {pat['rs']:+.1f}%" if pat.get("rs") is not None else "趨勢判斷"])
    out.append(["炒作風險", clamp(100 - sv["hype"]), f"炒作風險 {sv['hype']} 分（分數越高越安全）"])
    vals = [x[1] for x in out if x[1] is not None]
    weights = {"成長性": 1.3, "獲利能力": 1.3, "財務體質": 1, "評價": 1, "股利": 0.6, "籌碼": 1, "技術面": 0.9, "炒作風險": 1.2}
    tot = sum(x[1] * weights[x[0]] for x in out if x[1] is not None) / sum(weights[x[0]] for x in out if x[1] is not None) if vals else 0
    return {"items": [[k, s, grade(s) if s is not None else "-", t] for k, s, t in out], "total": round(tot), "grade": grade(tot)}


# ---------------------------------------------------------------- 即時報價
def live_quotes(codes):
    chans = []
    for c in codes:
        if c in ("t00", "o00"):
            chans.append(("tse_" if c == "t00" else "otc_") + c + ".tw")
            continue
        s = HIST.get(c)
        mk = "otc_" if s and s["market"] == "上櫃" else "tse_"
        chans.append(f"{mk}{c}.tw")
    out = {}
    for i in range(0, len(chans), 40):
        q = urllib.parse.quote("|".join(chans[i:i + 40]), safe="")
        url = f"https://mis.twse.com.tw/stock/api/getStockInfo.jsp?ex_ch={q}&json=1&delay=0&_={int(time.time() * 1000)}"
        try:
            js = http_get(url, timeout=10, retries=2)
        except Exception as e:
            print("  ! 即時報價失敗", e)
            continue
        for m in js.get("msgArray", []):
            y = num(m.get("y"))
            z = num(m.get("z"))
            if z is None:   # 尚未成交或瞬間無成交，用最佳買價
                b = (m.get("b") or "").split("_")[0]
                z = num(b) or num(m.get("pz")) or num(m.get("o"))
            if z is None:
                z = y
            lv = lambda pk, vk: [[num(a), num(b)] for a, b in zip((m.get(pk) or "").split("_"), (m.get(vk) or "").split("_")) if num(a)]
            out[m.get("c")] = {"price": z, "y": y, "o": num(m.get("o")), "h": num(m.get("h")), "l": num(m.get("l")),
                              "v": num(m.get("v")), "tv": num(m.get("tv")), "time": m.get("t") or m.get("%"), "d": m.get("d"),
                              "chg_pct": round((z / y - 1) * 100, 2) if z and y else None, "name": m.get("n"),
                              "asks": lv("a", "f")[:5], "bids": lv("b", "g")[:5]}
    return out


# ---------------------------------------------------------------- 網頁伺服器
class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, body, ctype="application/json; charset=utf-8", code=200):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False)
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        q = urllib.parse.parse_qs(u.query)
        try:
            if u.path == "/":
                self.send(full_page(), "text/html; charset=utf-8")
            elif u.path == "/api/status":
                self.send(STATUS)
            elif u.path == "/api/report":
                self.send(REPORT if REPORT else {"error": "not ready"})
            elif u.path == "/api/live":
                codes = [c for c in q.get("codes", [""])[0].split(",") if c][:200]
                self.send(live_quotes(codes))
            elif u.path == "/api/stock":
                code = q.get("code", [""])[0].strip()
                if not code.isdigit():
                    # 以名稱搜尋
                    for c, s in HIST.items():
                        if s["name"] == code or code in s["name"]:
                            code = c
                            break
                o = stock_detail(code)
                self.send(o if o else {"error": f"找不到 {code} 或資料不足"})
            elif u.path == "/api/refresh":
                if STATUS["state"] != "loading":
                    threading.Thread(target=safe_update, daemon=True).start()
                self.send({"ok": True})
            else:
                self.send({"error": "not found"}, code=404)
        except Exception as e:
            traceback.print_exc()
            self.send({"error": str(e)}, code=500)


def safe_update():
    try:
        update_data()
    except Exception as e:
        traceback.print_exc()
        STATUS.update(state="error", msg=f"資料更新失敗: {e}")


PAGE = r"""<title>台股每日分析</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Chiron+GoRound+TC:wght@600;800&display=swap">
<style>
/* 活潑明亮：天空藍底、白卡片、陽光黃重點色，橘白貓橘橘陪伴；紅漲綠跌 */
:root{--bg:#eef6ff;--hdr:#ffffff;--card:#ffffff;--card2:#f2f7ff;--line:#d7e3f5;--txt:#1f2a44;--mut:#5f6f8c;
--up:#e8364f;--down:#13a35b;--acc:#ffc23c;--blue:#3d8bfd;--chip:#e7effb;--chiptxt:#33476b;--ink:#1f2a44;--scrim:rgba(15,25,45,.55);--good:#3d8bfd;--bad:#ff6b3d;
--coral:#ff6b6b;--mint:#22c3a6;--grape:#9b5de5;--onacc:#ffffff;color-scheme:light}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#0f1622;--hdr:#151e2d;--card:#182233;--card2:#1f2b3f;--line:#2b3a52;--txt:#e6edf8;--mut:#9aa9c2;
--up:#ff5a6e;--down:#2fd27a;--chip:#26344b;--chiptxt:#c9d6ea;--ink:#111;--scrim:rgba(0,0,0,.65);--good:#5aa2ff;--bad:#ff7a45;color-scheme:dark}}
:root[data-theme="dark"]{--bg:#0f1622;--hdr:#151e2d;--card:#182233;--card2:#1f2b3f;--line:#2b3a52;--txt:#e6edf8;--mut:#9aa9c2;
--up:#ff5a6e;--down:#2fd27a;--chip:#26344b;--chiptxt:#c9d6ea;--ink:#111;--scrim:rgba(0,0,0,.65);--good:#5aa2ff;--bad:#ff7a45;color-scheme:dark}
[hidden]{display:none!important}
h1,h2,h3,.tab,.fun{font-family:"Chiron GoRound TC",-apple-system,"PingFang TC","Microsoft JhengHei","Noto Sans TC",sans-serif}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--txt);
font-family:-apple-system,"PingFang TC","Microsoft JhengHei","Noto Sans TC",sans-serif;font-size:14px}
body::before{content:"";position:fixed;inset:0 0 auto;height:env(safe-area-inset-top,0px);z-index:10;background:var(--hdr)}
header{display:flex;align-items:center;gap:12px 16px;flex-wrap:wrap;padding-block:12px;border-bottom:1px solid var(--line);
padding-left:max(16px,env(safe-area-inset-left,0px));padding-right:max(16px,env(safe-area-inset-right,0px));
background:var(--hdr);position:sticky;top:env(safe-area-inset-top,0px);z-index:5;border-bottom:3px solid var(--acc)}
h1{font-size:19px;margin:0}.mut{color:var(--mut)}.up{color:var(--up)}.down{color:var(--down)}
.pill{padding:3px 10px;border-radius:99px;background:var(--card2);font-size:12px}
.live-dot{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--mut);margin-right:6px}
.live-dot.on{background:var(--up);animation:b 1.2s infinite}@keyframes b{50%{opacity:.3}}
main{max-width:1320px;margin:0 auto;padding-block:18px 60px;padding-left:max(16px,env(safe-area-inset-left,0px));padding-right:max(16px,env(safe-area-inset-right,0px))}
.grid{display:grid;gap:14px}.g4{grid-template-columns:repeat(auto-fit,minmax(220px,1fr))}
.card{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:14px 16px;box-shadow:0 2px 0 var(--line)}
.big{font-size:26px;font-weight:700;font-variant-numeric:tabular-nums}
h2{font-size:17px;margin:26px 0 4px}.sub{color:var(--mut);margin:0 0 12px;font-size:13px}
.tabs{display:flex;gap:6px;margin:22px 0 12px;flex-wrap:wrap}
.tab{background:var(--card2);border:1px solid var(--line);color:var(--txt);padding:8px 14px;border-radius:8px;cursor:pointer;font-size:14px}
.tab.on{background:var(--acc);color:var(--ink);border-color:var(--acc);font-weight:600}
.stocks{display:grid;gap:12px;grid-template-columns:repeat(auto-fill,minmax(360px,1fr))}
.st{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:14px;box-shadow:0 2px 0 var(--line)}
.st .top{display:flex;justify-content:space-between;align-items:flex-start;gap:8px}
.st .nm{font-size:16px;font-weight:700}.st .cd{color:var(--mut);font-size:12px;margin-left:6px}
.price{text-align:right;font-variant-numeric:tabular-nums}.price .p{font-size:20px;font-weight:700}
.plan{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin:10px 0}
.plan div{background:var(--card2);border-radius:8px;padding:6px 8px}.plan b{display:block;font-size:14px;font-variant-numeric:tabular-nums}
.plan small{color:var(--mut);font-size:11px}
.why{display:flex;flex-wrap:wrap;gap:5px;margin-top:8px}.why span{font-size:11.5px;background:var(--chip);padding:2px 8px;border-radius:6px;color:var(--chiptxt)}
.status{margin-top:8px;font-size:13px;padding:6px 10px;border-radius:8px;background:var(--card2)}
.score{font-size:11px;background:var(--acc);color:var(--ink);border-radius:6px;padding:1px 6px;margin-left:6px;font-weight:700}
table{width:100%;border-collapse:collapse;font-variant-numeric:tabular-nums}
th,td{padding:7px 8px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}
th:first-child,td:first-child,th:nth-child(2),td:nth-child(2){text-align:left}th{color:var(--mut);font-weight:500;font-size:12px}
tr.click{cursor:pointer}tr.click:hover{background:var(--card2)}
.tbls .card{overflow-x:auto}
.tbls{display:grid;gap:14px;grid-template-columns:repeat(auto-fit,minmax(300px,1fr))}
input{background:var(--card2);border:1px solid var(--line);color:var(--txt);padding:8px 12px;border-radius:8px;font-size:14px;width:200px}
button.b{background:var(--blue);border:0;color:var(--onacc);font-weight:700;padding:8px 14px;border-radius:8px;cursor:pointer;font-size:14px}
button.g{background:var(--card2);border:1px solid var(--line);color:var(--txt);padding:6px 10px;border-radius:8px;cursor:pointer;font-size:12px}
.loading{max-width:520px;margin:120px auto;text-align:center}.bar{height:8px;background:var(--card2);border-radius:9px;overflow:hidden;margin:16px 0}
.bar i{display:block;height:100%;background:var(--acc);transition:width .4s}
.warn{font-size:12px;color:var(--mut);margin-top:30px;line-height:1.7;border-top:1px solid var(--line);padding-top:12px}
#modal{position:fixed;inset:0;background:var(--scrim);display:none;align-items:center;justify-content:center;z-index:20;padding:16px}
#modal .box{max-width:780px;width:100%;max-height:92vh;overflow:auto}
.sec{margin-top:16px;border-top:1px solid var(--line);padding-top:12px}.sec h3{font-size:15px;margin:0 0 8px}
.sec ul{margin:4px 0 8px;padding-left:20px;line-height:1.75}.sec h4{margin:10px 0 2px;font-size:13px;color:var(--mut);font-weight:600}
.rating{display:inline-block;font-weight:700;padding:3px 12px;border-radius:99px;background:var(--card2);margin-right:8px}
.rating.up{background:var(--up);color:#fff}.rating.down{background:var(--down);color:var(--ink)}
.summary{background:var(--card2);border-radius:10px;padding:10px 12px;line-height:1.7;margin-top:8px}
.tblwrap{overflow-x:auto}.ai{line-height:1.8;white-space:normal}.ai h4{color:var(--acc)}
.filters{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:10px}.filters input{flex:1 1 180px;width:auto;min-width:0}
select{background:var(--card2);border:1px solid var(--line);color:var(--txt);padding:8px;border-radius:8px;font-size:14px;max-width:100%}
.more{display:block;margin:12px auto 0}
.sv{display:flex;flex-wrap:wrap;align-items:center;gap:6px 10px;margin-top:8px;font-size:12.5px;padding:6px 10px;border-radius:8px;background:var(--card2)}
.vtag{font-weight:700;padding:1px 8px;border-radius:6px;background:var(--chip)}
.vtag.ok{background:var(--good);color:var(--ink)}.vtag.warn{background:var(--acc);color:var(--ink)}.vtag.bad{background:var(--bad);color:var(--ink)}.vtag.weak{color:var(--mut)}
.verdict{display:grid;gap:10px;background:var(--card2);border-radius:12px;padding:12px 14px;margin-top:10px}
.verdict .big{font-size:22px}.meter{display:grid;grid-template-columns:72px 1fr 40px;align-items:center;gap:8px;font-size:12.5px}
.meter i{display:block;height:8px;border-radius:9px;background:var(--line);overflow:hidden}.meter i b{display:block;height:100%}
.checks{list-style:none;padding:0;margin:0;display:grid;gap:4px;font-size:13px;line-height:1.5}
.checks li{display:grid;grid-template-columns:20px 1fr;gap:4px}
.c-ok{color:var(--good)}.c-bad{color:var(--bad)}.c-warn{color:var(--acc)}
.theme{display:inline-block;font-size:11.5px;padding:2px 8px;border-radius:6px;border:1px solid var(--acc);color:var(--acc)}
.news{display:grid;gap:10px}.news .n{background:var(--card2);border-radius:8px;padding:8px 10px;font-size:13px;line-height:1.6}
.news .n a{color:var(--blue)}.senti{font-size:11px;padding:1px 6px;border-radius:5px;margin-right:6px;background:var(--chip)}
.senti.pos{color:var(--up)}.senti.neg{color:var(--down)}
.card8{display:grid;gap:6px}.c8{display:grid;grid-template-columns:64px 26px 1fr;gap:8px;align-items:center;font-size:12.5px}
.c8 i{display:block;height:7px;border-radius:9px;background:var(--line);overflow:hidden}.c8 i b{display:block;height:100%;background:var(--blue)}
.gr{display:inline-grid;place-items:center;width:24px;height:22px;border-radius:6px;font-weight:800;font-size:13px;background:var(--chip)}
.gA{background:var(--good);color:var(--ink)}.gB{background:#7fd1ff;color:var(--ink)}.gC{background:var(--chip)}.gD{background:var(--acc);color:var(--ink)}.gE{background:var(--bad);color:var(--ink)}
.bigg{width:46px;height:46px;font-size:26px;border-radius:12px}
.chart{width:100%;height:auto;display:block;margin-top:8px;background:var(--card2);border-radius:10px}
.legend{display:flex;flex-wrap:wrap;gap:10px;font-size:11.5px;color:var(--mut);margin-top:4px}.legend b{display:inline-block;width:12px;height:3px;vertical-align:middle;margin-right:4px}
.evt{font-size:12.5px;line-height:1.6;border-bottom:1px dashed var(--line);padding:6px 0}
#newsbox{margin-top:14px}#newsbox p{margin:4px 0;line-height:1.7}
.kv{display:grid;grid-template-columns:repeat(3,1fr);gap:6px;margin-top:10px}.kv div{background:var(--card2);padding:6px 8px;border-radius:8px;font-size:12px}
.kv b{display:block;font-size:14px}
.logo{display:flex;align-items:center;gap:6px}.logo svg,.logo img{width:38px;height:38px}#logoCat{display:inline-block;width:38px;height:38px}
.catbtn{position:fixed;right:calc(14px + env(safe-area-inset-right,0px));bottom:calc(14px + env(safe-area-inset-bottom,0px));z-index:18;border:3px solid var(--acc);background:var(--card);border-radius:50%;width:70px;height:70px;padding:4px;cursor:pointer;box-shadow:0 6px 18px rgba(0,0,0,.18)}
.catbtn svg,.catbtn img{width:100%;height:100%}#catface{display:block;width:100%;height:100%}.catbtn .badge{position:absolute;top:-6px;right:-6px;background:var(--coral);color:#fff;border-radius:99px;font-size:11px;font-weight:800;padding:1px 6px}
.catbtn .bub{position:absolute;right:76px;bottom:12px;background:var(--card);border:2px solid var(--acc);border-radius:14px;padding:6px 10px;font-size:13px;white-space:nowrap;color:var(--txt);box-shadow:0 3px 10px rgba(0,0,0,.12)}
.chat{position:fixed;right:calc(14px + env(safe-area-inset-right,0px));bottom:calc(92px + env(safe-area-inset-bottom,0px));z-index:19;width:min(430px,calc(100vw - 28px));height:min(72vh,600px);
  background:var(--card);border:2px solid var(--acc);border-radius:22px;display:flex;flex-direction:column;overflow:hidden;box-shadow:0 12px 34px rgba(0,0,0,.22)}
.chat header{position:static;border:0;padding:8px 12px;background:linear-gradient(90deg,#ffe7b8,#ffd3dc);color:#3a2a10;display:flex;gap:8px;align-items:center}
.chat header svg,.chat header img{width:40px;height:40px}#chatcat{display:inline-block;width:40px;height:40px;flex:none}.msgs{flex:1;overflow:auto;padding:12px;display:grid;gap:10px;align-content:start}
.m{max-width:88%;padding:8px 12px;border-radius:16px;font-size:14px;line-height:1.65}.m.me{justify-self:end;background:var(--blue);color:#fff;border-bottom-right-radius:4px}
.m.bot{justify-self:start;background:var(--card2);border-bottom-left-radius:4px}.m.bot ul{margin:4px 0;padding-left:18px}
.chips{display:flex;gap:6px;flex-wrap:wrap;padding:0 12px 8px}.chips button{font-size:12px;border:1px solid var(--line);background:var(--card2);color:var(--txt);border-radius:99px;padding:4px 10px;cursor:pointer}
.chatin{display:flex;gap:6px;padding:10px;border-top:1px solid var(--line)}.chatin input{flex:1;min-width:0;width:auto}
.dec{font-weight:800;font-size:15px;margin-bottom:4px}
.toast{position:fixed;left:50%;transform:translateX(-50%);top:calc(70px + env(safe-area-inset-top,0px));z-index:25;background:var(--card);border:2px solid var(--acc);border-radius:16px;padding:8px 14px;display:flex;gap:8px;align-items:center;box-shadow:0 8px 24px rgba(0,0,0,.2);max-width:calc(100vw - 32px)}
.toast svg,.toast img{width:40px;height:40px;flex:none}
.five{display:grid;grid-template-columns:1fr 1fr;gap:8px;font-variant-numeric:tabular-nums;font-size:13px}.five table td{padding:3px 6px}
.vbar{display:inline-block;height:8px;border-radius:4px;vertical-align:middle;margin-left:4px}
.alertlist{display:grid;gap:6px;margin-top:8px}.alertlist div{background:var(--card2);border-radius:10px;padding:6px 10px;font-size:13px}
@media (max-width:520px){.stocks{grid-template-columns:1fr}.plan{grid-template-columns:repeat(2,1fr)}header .sp{display:none}input{flex:1 1 150px;width:auto;min-width:0}h1{font-size:17px}}
</style>
<header>
  <h1 class="logo"><span id="logoCat"></span>台股每日分析</h1>
  <span class="pill"><span id="dot" class="live-dot"></span><span id="livetxt">連線中</span></span>
  <span class="mut" id="dtxt"></span>
  <span class="sp" style="flex:1"></span>
  <input id="q" placeholder="輸入代號或名稱，如 2330">
  <button class="b" onclick="lookup()">查詢</button>
  <button class="g" id="refbtn" onclick="refreshData()" title="收盤後(約 15:00)重新抓今日資料">更新收盤資料</button>
  <button class="g" id="alertbtn" onclick="showAlerts()">🔔 買賣提醒</button>
  <button class="g" onclick="showPic()">🐱 換圖片</button>
  <a class="g" id="schoollink" href="school/" hidden style="text-decoration:none">📚 股票小學堂</a>
</header>
<div id="loading" class="loading"><h2>資料準備中…</h2><div class="bar"><i id="pb" style="width:0"></i></div>
<div class="mut" id="lmsg"></div></div>
<main id="app" style="display:none">
  <div class="grid g4" id="overview"></div>
  <div id="newsslot"></div>
  <div class="tabs" id="tabs"></div>
  <div id="panel"></div>
  <div class="warn">⚠️ 本工具依公開資料以技術面、籌碼面規則自動計算，僅供參考，不構成任何投資建議；投資前請自行判斷並控管風險。<br>
  進場區間 / 停損 / 目標價依 ATR(平均真實波幅)與均線計算；盤中資料來自證交所基本市況報導網站，可能有延遲。<br>
  推薦與潛力股以「前一個交易日收盤」資料計算，盤中會顯示即時價格相對於建議區間的位置。</div>
</main>
<div id="modal" onclick="if(event.target===this)closeModal()"><div class="box card" id="mbox"></div></div>
<button class="catbtn" id="catbtn" onclick="toggleChat()" aria-label="問橘橘分析師"><span id="catface"></span><span class="bub" id="catbub">問我股票能不能買～</span><span class="badge" id="catbadge" hidden>!</span></button>
<div class="chat" id="chat" hidden><header><span id="chatcat"></span><div><b class="fun">橘橘分析師</b><div style="font-size:12px">輸入股票名稱，問我能不能買、何時賣</div></div><span style="flex:1"></span><button class="g" onclick="toggleChat()" aria-label="關閉">✕</button></header>
<div class="msgs" id="msgs"></div><div class="chips" id="chips"></div>
<form class="chatin" onsubmit="event.preventDefault();sendChat()"><input id="chatq" placeholder="例如：台積電可以買嗎？" autocomplete="off"><button class="b">送出</button></form></div>
<script>
let R=null, LIVE={}, TAB='momentum', CUR=null;
const S=window.__TW_STATIC__||null;   // 雲端(手機)版: 資料直接內嵌在網頁裡
const NATIVE=window.TWNative||null;   // Android App: 可直接連證交所即時報價
const SITE=!!(S&&!window.claude&&(location.protocol==='https:'||NATIVE));  // 免費網站版 (GitHub Pages) 或 Android App
function nativeLive(codes){
  const all=Object.fromEntries((R?R.all:[]).map(r=>[r[0],r[2]]));
  const ch=codes.map(c=>c==='t00'?'tse_t00.tw':c==='o00'?'otc_o00.tw':(all[c]==='上櫃'?'otc_':'tse_')+c+'.tw'),out={};
  for(let i=0;i<ch.length;i+=40){
    let js;try{js=JSON.parse(NATIVE.get('https://mis.twse.com.tw/stock/api/getStockInfo.jsp?ex_ch='+encodeURIComponent(ch.slice(i,i+40).join('|'))+'&json=1&delay=0&_='+Date.now()))}catch(e){continue}
    (js.msgArray||[]).forEach(m=>{const n=x=>{const v=parseFloat(String(x).replace(/,/g,''));return isNaN(v)?null:v};const y=n(m.y);let z=n(m.z);if(z==null)z=n((m.b||'').split('_')[0])||n(m.pz)||n(m.o)||y;
      const lv=(pk,vk)=>(m[pk]||'').split('_').map((p,j)=>[n(p),n((m[vk]||'').split('_')[j])]).filter(x=>x[0]).slice(0,5);
      out[m.c]={price:z,y,o:n(m.o),h:n(m.h),l:n(m.l),v:n(m.v),tv:n(m.tv),time:m.t||m['%'],d:m.d,chg_pct:z&&y?Math.round((z/y-1)*10000)/100:null,name:m.n,asks:lv('a','f'),bids:lv('b','g')}})}
  return out;
}
async function api(path){
  if(!S)return (await fetch(path)).json();
  const u=new URL(path,'http://x'),q=u.searchParams.get('code')||'';
  if(u.pathname==='/api/status')return{state:'ready',progress:100,msg:''};
  if(u.pathname==='/api/report')return S.report;
  if(u.pathname==='/api/live')return NATIVE?nativeLive((u.searchParams.get('codes')||'').split(',').filter(Boolean)):(S.live||{});
  if(u.pathname==='/api/stock'){const ks=Object.keys(S.stocks);
    const c=S.stocks[q]?q:ks.find(k=>S.stocks[k].name===q)||ks.find(k=>S.stocks[k].name.includes(q));
    return c?S.stocks[c]:{error:'找不到「'+q+'」，請輸入上市櫃股票代號或名稱'}}
  return{};
}
const WATCH_KEY='tw_watch';
function getHold(){try{return JSON.parse(localStorage.getItem('tw_hold')||'{}')}catch(e){return{}}}
function setHold(h){try{localStorage.setItem('tw_hold',JSON.stringify(h))}catch(e){}}
function getBudget(){try{return +localStorage.getItem('tw_budget')||100000}catch(e){return 100000}}
function setBudget(v){try{localStorage.setItem('tw_budget',Math.max(0,+v||0))}catch(e){}render()}
const isFundLike=c=>/^0/.test(c);
// 交易成本：手續費 0.1425%（買賣各一次），證交稅股票 0.3%、ETF 0.1%
function netPL(code,cost,qty,price){const buy=cost*qty*(1+0.001425),sell=price*qty*(1-0.001425-(isFundLike(code)?0.001:0.003));return{buy,sell,pl:sell-buy,pct:(sell/buy-1)*100}}
function myStop(d,h){const pl=d.plan,L=LIVE[d.code],px=L&&L.price?L.price:d.close;
  // 空頭時的計畫停損是給「站回月線才買」用的，持股改用近 20 日低點
  const base=pl.trend==='空頭'&&px<pl.entry_lo?Math.min(pl.stop,Math.round((d.low20||px)*0.98*100)/100):pl.stop;
  return px>=h.price*1.1?Math.max(base,h.price):Math.max(base,Math.round(h.price*0.92*100)/100)}
function longTarget(d){const t=d.rep&&d.rep.target;if(t&&t>d.close)return{v:t,src:'依 EPS × 合理本益比估算的合理價'};
  const hi=d.high60||d.plan.t2;const v=Math.max(hi,d.plan.t2)*1.1;return{v:Math.round(v*100)/100,src:'60 日高點突破後的下一個壓力（技術面估算）'}}
function buyAdvice(d,price){const pl=d.plan,rt=(d.rep||{}).rating,v=(d.sv||{}).verdict;
  if(v==='疑似炒作')return['先不要買','down','炒作風險高，股價可能被短線資金拉抬'];
  if(pl.trend==='空頭')return['等待','',`趨勢偏弱，等站回月線 ${f(d.ma20)} 再考慮`];
  if(price<pl.stop)return['先不要買','down',`已跌破支撐 ${f(pl.stop)}，等止跌再看`];
  if(price>pl.entry_hi*1.02)return['等拉回再買','',`現在比建議區高，等回到 ${f(pl.entry_lo)}~${f(pl.entry_hi)} 再買`];
  if(rt==='觀望 / 減碼')return['等待','','分析師評等偏保守，可以小量試單或等訊號'];
  return['可以買進','up',`價格在建議區 ${f(pl.entry_lo)}~${f(pl.entry_hi)} 附近，可分 2～3 次買`]}
function suggestQty(d,price){const B=getBudget(),pl=d.plan,mood=(R.market||{}).mood;
  const cap={'多頭':0.3,'偏多震盪':0.2,'短線轉弱':0.15,'空頭':0.1}[mood]||0.2;
  const risk=Math.max(price-pl.stop,price*0.02);let q=Math.floor(B*0.02/risk);q=Math.min(q,Math.floor(B*cap/price));
  return{q:Math.max(q,0),cap}}
function qtyTxt(q){const z=Math.floor(q/1000),r=q%1000;return (z?z+' 張':'')+(z&&r?' ':'')+(r?r+' 股':'')||'0 股'}
function holdBox(d){
  const h=getHold()[d.code],L=LIVE[d.code],price=L&&L.price?L.price:d.close,pl=d.plan,lt=longTarget(d),st=e=>'onclick="event.stopPropagation()"';
  const tg=`<div class="kv2" style="display:grid;grid-template-columns:1fr 1fr;gap:6px;margin:6px 0">
    <div class="card" style="padding:8px"><small class="mut">短期目標（1～4 週）</small><br><b class="up">${f(pl.t1)}</b> → <b class="up">${f(pl.t2)}</b></div>
    <div class="card" style="padding:8px"><small class="mut">長期目標（6～12 個月）</small><br><b class="up">${f(lt.v)}</b> <small class="mut">${sg((lt.v/price-1)*100)}${f((lt.v/price-1)*100,1)}%</small></div></div>
    <div class="mut" style="font-size:11px">長期目標：${lt.src}</div>`;
  if(!h){const [a,ac,why]=buyAdvice(d,price),sq=suggestQty(d,price),q=ac==='down'?0:sq.q;
    return `<div class="sec" ${st()} style="margin-top:10px;border-top:1px dashed var(--line);padding-top:8px"><b>要不要買？</b> <span class="vtag ${ac==='up'?'ok':ac==='down'?'bad':'warn'}">${a}</span>
      <div style="font-size:13px;margin:4px 0">${why}</div>
      ${q?`<div style="font-size:13px">💵 建議買 <b>${qtyTxt(q)}</b>，約 <b>${f(q*price,0)}</b> 元（資金 ${f(getBudget(),0)} 元的 ${f(q*price/getBudget()*100,0)}%；跌到停損 ${f(pl.stop)} 最多虧約 ${f(q*(price-pl.stop),0)} 元）</div>
        <div class="mut" style="font-size:11px">算法：每檔最多虧總資金 2%，單檔不超過資金 ${sq.cap*100}%（依大盤${(R.market||{}).mood||''}調整）</div>`:''}
      ${tg}
      <div style="display:flex;gap:6px;flex-wrap:wrap;align-items:center;margin-top:6px;font-size:13px">我已買進：價格 <input id="hp_${d.code}" type="number" step="0.01" value="${price}" style="width:80px">
        股數 <input id="hq_${d.code}" type="number" value="${q||1000}" style="width:80px"><button class="g" onclick="event.stopPropagation();saveHold('${d.code}')">記錄買進</button></div></div>`}
  const n=netPL(d.code,h.price,h.qty,price),stop=myStop(d,h);let a,ac,why;
  if(price<=stop){a='建議停損';ac='bad';why=`現價 ${f(price)} 已跌破停損 ${f(stop)}，建議賣出，保住本金`}
  else if(price>=pl.t2){a='獲利了結';ac='ok';why=`已到短期第二目標 ${f(pl.t2)}，建議賣出大部分；看好長期可留一點到 ${f(lt.v)}`}
  else if(price>=pl.t1){a='先賣一半';ac='ok';why=`已到短期第一目標 ${f(pl.t1)}，先賣一半，剩下的停損移到成本 ${f(h.price)}`}
  else if(pl.trend==='空頭'){a='減碼 / 設好停損';ac='warn';why=`趨勢偏弱，反彈到月線 ${f(d.ma20)} 附近可以減碼，跌破 ${f(stop)} 就停損`}
  else{a='續抱等待';ac='ok';why=`趨勢沒有轉壞，繼續持有，等漲到 ${f(pl.t1)}；跌破 ${f(stop)} 才停損`}
  return `<div class="sec" ${st()} style="margin-top:10px;border-top:1px dashed var(--line);padding-top:8px"><b>我的持股</b> <span class="vtag ${ac}">${a}</span>
    <div style="font-size:13px;margin:4px 0">${why}</div>
    <div style="font-size:13px;line-height:1.7">買進 ${f(h.price)} × ${qtyTxt(h.qty)}，成本約 <b>${f(n.buy,0)}</b> 元（${h.date||''}）<br>
      現在市值約 ${f(price*h.qty,0)} 元，扣手續費和稅後 <b class="${cls(n.pl)}">${sg(n.pl)}${f(n.pl,0)} 元（${sg(n.pct)}${f(n.pct,1)}%）</b><br>
      🛑 我的停損價 <b class="down">${f(stop)}</b>${price>=h.price*1.1?'（已賺 10% 以上，停損移到成本，保住獲利）':''}</div>
    ${tg}
    <div style="margin-top:6px;text-align:right"><button class="g" onclick="event.stopPropagation();delHold('${d.code}')">已賣出 / 清除紀錄</button></div></div>`
}
function saveHold(c){const p=+$('#hp_'+c).value,q=Math.round(+$('#hq_'+c).value);if(!(p>0&&q>0)){toast('請輸入買進價格和股數');return}
  const h=getHold();h[c]={price:p,qty:q,date:new Date().toLocaleDateString('zh-TW')};setHold(h);toast('已記錄，橘橘會幫你盯停損和目標價！');syncNativeWatch();render()}
function delHold(c){const h=getHold();delete h[c];setHold(h);syncNativeWatch();render()}
function getWatch(){try{return JSON.parse(localStorage.getItem(WATCH_KEY)||'[]')}catch(e){return[]}}
function setWatch(w){try{localStorage.setItem(WATCH_KEY,JSON.stringify(w))}catch(e){}}
const $=s=>document.querySelector(s);
const f=(x,d=2)=>x==null||isNaN(x)?'-':Number(x).toLocaleString('zh-TW',{minimumFractionDigits:d,maximumFractionDigits:d});
const cls=x=>x>0?'up':x<0?'down':'';
const sg=x=>x>0?'+':'';
function inSession(){const n=new Date(),d=n.getDay(),m=n.getHours()*60+n.getMinutes();return d>0&&d<6&&m>=8*60+55&&m<=13*60+35}

async function boot(){
  for(;;){
    const s=await (await api('/api/status'));
    $('#pb').style.width=s.progress+'%';$('#lmsg').textContent=s.msg;
    if(s.state==='ready')break;
    if(s.state==='error'){$('#lmsg').innerHTML='<span class=up>'+s.msg+'</span>';return}
    await new Promise(r=>setTimeout(r,1000));
  }
  R=await (await api('/api/report'));
  $('#loading').style.display='none';$('#app').style.display='block';
  $('#dtxt').textContent='分析資料日：'+R.date;
  render();pollLive();
}

function spark(arr,w=110,h=32){
  if(!arr||arr.length<2)return'';const mn=Math.min(...arr),mx=Math.max(...arr),r=mx-mn||1;
  const pts=arr.map((v,i)=>(i/(arr.length-1)*w).toFixed(1)+','+(h-(v-mn)/r*h).toFixed(1)).join(' ');
  const col=arr[arr.length-1]>=arr[0]?'var(--up)':'var(--down)';
  return `<svg width="${w}" height="${h}" viewBox="0 0 ${w} ${h}"><polyline fill="none" stroke="${col}" stroke-width="1.6" points="${pts}"/></svg>`
}

function overview(){
  const m=R.market,b=R.breadth,L=LIVE['t00'],O=LIVE['o00'];
  const tp=L&&L.price?L.price:m.taiex, tc=L&&L.chg_pct!=null?L.chg_pct:m.taiex_chg_pct;
  const moodCol={'多頭':'up','偏多震盪':'up','短線轉弱':'down','空頭':'down'}[m.mood]||'';
  $('#overview').innerHTML=`
   <div class="card"><div class="mut">加權指數 ${L?'(即時 '+(L.time||'')+')':'(收盤)'}</div>
     <div class="big ${cls(tc)}">${f(tp)}</div><div class="${cls(tc)}">${sg(tc)}${f(tc)}%</div>
     ${spark((m.series||[]).map(x=>x[1]),200,36)}</div>
   <div class="card"><div class="mut">櫃買指數 ${O?'('+(O.time||'')+')':''}</div>
     <div class="big ${O?cls(O.chg_pct):''}">${O?f(O.price):'-'}</div><div class="${O?cls(O.chg_pct):''}">${O&&O.chg_pct!=null?sg(O.chg_pct)+f(O.chg_pct)+'%':''}</div></div>
   <div class="card"><div class="mut">大盤趨勢</div><div class="big ${moodCol}">${m.mood||'-'}</div>
     <div class="mut" style="font-size:12px">月線 ${f(m.ma20)}｜季線 ${f(m.ma60)}</div><div style="margin-top:6px">💡 ${m.position||''}</div></div>
   <div class="card"><div class="mut">漲跌家數 (${R.date})</div>
     <div class="big"><span class="up">${b.up}</span> <span class="mut" style="font-size:16px">/</span> <span class="down">${b.down}</span></div>
     <div class="mut">平盤 ${b.flat}｜推薦 ${R.momentum.length} 檔｜潛力 ${R.potential.length} 檔</div></div>`;
}

function liveStatus(s){
  const L=LIVE[s.code];if(!L||!L.price)return'';const p=L.price,pl=s.plan;let t,c;
  if(pl.trend==='空頭'&&p<pl.entry_lo){t='📉 空頭格局，等站回月線 '+f(pl.entry_lo)+' 再考慮進場';c='down'}
  else if(p<=pl.stop){t='⛔ 已跌破停損價，不宜進場 / 持有者應停損';c='down'}
  else if(p>=pl.t2){t='🎯 已達第二目標，可獲利出場';c='up'}
  else if(p>=pl.t1){t='🎯 已達第一目標，可分批獲利了結';c='up'}
  else if(p>=pl.entry_lo&&p<=pl.entry_hi){t='✅ 目前價格在建議進場區間內';c='up'}
  else if(p>pl.entry_hi){t='⏳ 高於進場區，不追高，等拉回 '+f(pl.entry_hi);c=''}
  else{t='👀 低於進場區，觀察能否守住 '+f(pl.stop);c=''}
  return `<div class="status ${c}">即時 ${L.time||''}：${t}</div>`
}

function stockCard(s){
  const L=LIVE[s.code],p=L&&L.price?L.price:s.close,c=L&&L.chg_pct!=null?L.chg_pct:s.chg_pct,pl=s.plan;
  const w=getWatch().includes(s.code);
  return `<div class="st"><div class="top"><div><span class="nm">${s.name}</span><span class="cd">${s.code}・${s.market}</span>
    <span class="score">${s.score}分</span>${s.grade||s.card?`<span class="gr g${s.grade||s.card.grade}" style="margin-left:6px" title="分析師總評">${s.grade||s.card.grade}</span>`:''}
    <div style="margin-top:4px">${spark(s.spark||(s.ohlc||[]).slice(-40).map(x=>x[3]))}</div></div>
    <div class="price"><div class="p ${cls(c)}">${f(p)}</div><div class="${cls(c)}">${sg(c)}${f(c)}%</div>
    <div class="mut" style="font-size:11px">${L&&L.v?'量 '+f(L.v,0)+' 張':'量 '+f(s.vol,0)+' 張'}</div></div></div>
    <div class="plan"><div><small>建議進場</small><b class="up">${f(pl.entry_lo)}~${f(pl.entry_hi)}</b></div>
      <div><small>停損 (${pl.stop_pct}%)</small><b class="down">${f(pl.stop)}</b></div>
      <div><small>目標一 (+${pl.t1_pct}%)</small><b>${f(pl.t1)}</b></div>
      <div><small>目標二</small><b>${f(pl.t2)}</b></div></div>
    <div class="mut" style="font-size:12px">風報比 ${pl.rr??'-'}｜RSI ${f(s.rsi,0)}｜月線 ${f(s.ma20)}｜外資5日 <span class="${cls(s.f5)}">${f(s.f5,0)}</span>｜投信5日 <span class="${cls(s.t5)}">${f(s.t5,0)}</span>
      ${s.pe?'｜PE '+f(s.pe,1):''}</div>
    ${pl.note?`<div class="status">${pl.note}</div>`:''}
    ${svRow(s)}
    <div class="why">${s.why.map(x=>'<span>'+x+'</span>').join('')}</div>${liveStatus(s)}
    <div style="margin-top:8px;text-align:right"><button class="g" onclick="toggleWatch('${s.code}')">${w?'★ 移出自選':'☆ 加入自選'}</button></div></div>`
}

function svRow(s){
  if(!s.sv)return'';const v=s.sv;
  return `<div class="sv"><span class="vtag ${v.vc}">${v.verdict}</span>${v.strength==null?'':`<span>實力 <b>${v.strength}</b></span>`}<span>炒作風險 <b class="${v.hype_lv==='高'?'c-bad':v.hype_lv==='中'?'c-warn':''}">${v.hype_lv}</b></span>
    ${(s.themes||[]).map(t=>`<span class="theme">${t}</span>`).join('')}</div>`
}
const SENT={'正面':'pos','負面':'neg'};
function newsItems(arr){return (arr||[]).map(n=>`<div class="n"><span class="senti ${SENT[n.sentiment]||''}">${n.sentiment||'新聞'}</span><b>${n.title}</b>
  <div class="mut" style="font-size:12px">${n.source||''} ${n.date||''}</div>${n.summary?`<div>${n.summary}</div>`:''}${n.url?`<a href="${n.url}" target="_blank" rel="noopener">閱讀原文</a>`:''}</div>`).join('')}
function newsPanel(){
  const N=R.news;if(!N)return'';
  return `<div class="card" id="newsbox"><h3 style="margin:0 0 6px">今日新聞重點 <span class="mut" style="font-size:12px;font-weight:400">${N.date||''}</span></h3>
    ${N.market?`<p><b>台股：</b>${N.market}</p>`:''}${N.global?`<p><b>國際：</b>${N.global}</p>`:''}
    ${(N.headlines||[]).length?`<div style="display:grid;gap:4px;font-size:13.5px">${N.headlines.map(h=>`<div>・<a href="${h.url}" target="_blank" rel="noopener" style="color:var(--txt)">${h.title}</a> <span class="mut" style="font-size:12px">${h.source||''} ${h.date||''}</span></div>`).join('')}</div>`:''}
    ${(N.themes||[]).length?`<div style="margin-top:8px;display:grid;gap:8px">${N.themes.map(t=>`<div><span class="theme">${t.name}${t.heat?'・熱度'+t.heat:''}</span>
      <span style="font-size:13px"> ${t.summary||''}</span><div style="margin-top:4px;display:flex;flex-wrap:wrap;gap:6px">${(t.codes||[]).map(c=>{const r=R.all.find(x=>x[0]===c);return r?`<button class="g" onclick="lookup('${c}')">${r[1]} ${c}</button>`:''}).join('')}</div></div>`).join('')}</div>`:''}</div>`
}
function table(rows,cols){
  return `<table><tr>${cols.map(c=>'<th>'+c[0]+'</th>').join('')}</tr>${rows.map(r=>`<tr class="click" onclick="lookup('${r.code}')">${cols.map(c=>'<td>'+c[1](r)+'</td>').join('')}</tr>`).join('')}</table>`
}
const pctCell=r=>{const L=LIVE[r.code],c=L&&L.chg_pct!=null?L.chg_pct:r.chg_pct;return `<span class="${cls(c)}">${sg(c)}${f(c)}%</span>`};
const priceCell=r=>{const L=LIVE[r.code];return f(L&&L.price?L.price:r.close)};

let WATCH_DATA={};
function syncNativeWatch(){if(!NATIVE)return;try{NATIVE.saveWatch(JSON.stringify(getWatch().map(c=>WATCH_DATA[c]).filter(Boolean).map(d=>({code:d.code,name:d.name,market:d.market,...planOf(d.code)}))))}catch(e){}}
async function loadWatch(){
  for(const c of getWatch()){if(!WATCH_DATA[c]){const d=await (await api('/api/stock?code='+c));if(!d.error)WATCH_DATA[c]=d}}
  syncNativeWatch();
}
function toggleWatch(c){let w=getWatch();const on=!w.includes(c);w=on?[...w,c]:w.filter(x=>x!==c);setWatch(w);syncWatchDB(c,on);if(on)toast('已加入自選，到買賣點時橘橘會提醒你！');
  if(!w.includes(c))delete WATCH_DATA[c];loadWatch().then(()=>{render();pollLive(true)})}

function render(){
  overview();
  const tabs=[['momentum','🔥 今日推薦股'],['potential','💎 潛力股'],['daytrade','⚡ 當沖參考'],['etf','🏦 ETF 買賣'],['divs','💰 配息股'],['nolimit','🚀 無漲跌幅'],['all','📋 全部股票'],['watch','★ 自選股'],['rank','📊 排行榜']];
  $('#tabs').innerHTML=tabsHTML(tabs);
  if($('#newsslot'))$('#newsslot').innerHTML=newsPanel();
  if(TAB==='etf')setTimeout(fillEtf);if(TAB==='divs')setTimeout(fillDiv);
  if(TAB==='all'&&$('#alist')){$('#tabs').innerHTML=tabsHTML(tabs);fillAll();return}
  let h='';
  const bear=['空頭','短線轉弱'].includes(R.market.mood)?`<div class="status down" style="margin-bottom:12px">⚠️ 大盤目前為「${R.market.mood}」，個股推薦成功率會下降，${R.market.position}。</div>`:'';
  if(TAB==='momentum'){h=bear+`<p class="sub">強勢多頭：均線多頭排列、量價齊揚、法人買超。適合短線順勢操作，嚴守停損。</p>
    <div class="stocks">${R.momentum.map(stockCard).join('')||'<div class=mut>今日無符合條件的股票（大盤偏弱時正常）</div>'}</div>`}
  else if(TAB==='potential'){h=bear+`<p class="sub">蓄勢待發：剛站上月線、布林收斂、法人默默佈局，尚未大漲。適合分批佈局、中線持有。</p>
    <div class="stocks">${R.potential.map(stockCard).join('')||'<div class=mut>今日無符合條件的股票</div>'}</div>`}
  else if(TAB==='watch'){const w=getWatch();h=`<p class="sub">在上方查詢任一股票並加入自選，會每天自動給出進出場建議。</p>
    <div class="card" style="display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-bottom:10px">💰 我可以投入的資金
      <input id="budget" type="number" inputmode="numeric" value="${getBudget()}" style="width:130px" onchange="setBudget(this.value)"> 元
      <span class="mut" style="font-size:12px">（用來算每檔建議買多少）</span></div>
    <div class="stocks">${w.map(c=>WATCH_DATA[c]?stockCard(WATCH_DATA[c]).replace(/<\/div>$/,holdBox(WATCH_DATA[c])+'</div>'):'').join('')||'<div class=mut>尚未加入自選股</div>'}</div>`}
  else if(TAB==='daytrade'){const L=R.daytrade||[];
    h=`<div class="status down" style="margin-bottom:10px;color:var(--bad)">⚠️ 當沖風險非常高：一天內就要買賣完，股價一下跌可能虧很多，還要付手續費和證交稅（當沖證交稅 0.15%）。新手建議先在股票小學堂練習，不要直接上場。</div>
    <p class="sub">可以現股當沖、成交量大、波動夠的股票（已排除處置股）。每檔都列出「幾點、什麼價位進場」、停損、停利和最晚出場時間。價位是用昨天的最高、最低、收盤算出的樞紐點 PP / R1 / R2 / S1 / S2。</p>
    <div class="stocks">${L.map(r=>`<div class="card click" onclick="lookup('${r.code}')"><div style="display:flex;justify-content:space-between;align-items:center"><b>${r.name} <span class="mut">${r.code}</span></b>
      <span class="${r.trend==='偏多'?'up':r.trend==='偏空'?'down':''}">${r.trend}</span></div>
      <div class="mut" style="font-size:12px">昨收 ${f(r.close)}（<span class="${cls(r.chg_pct)}">${sg(r.chg_pct)}${f(r.chg_pct)}%</span>）・波動 ${f(r.atr_pct,1)}%・昨日當沖比 ${r.ratio!=null?f(r.ratio,1)+'%':'-'}・${r.susp?'只能先買後賣':'可雙向'}</div>
      ${dtPlan(r)}</div>`).join('')||'<div class=mut>今天沒有符合條件的股票</div>'}</div>
    <div class="mut" style="font-size:12px;margin-top:8px">波動＝平均每天的振幅（ATR ÷ 股價）；當沖比＝昨天當沖成交量占總成交量的比例，越高代表短線客越多。風報比＝可能賺的價差 ÷ 停損會虧的價差，大於 1.5 比較值得做。以上是依昨天資料算出的參考計畫，不是保證獲利。</div>`}
  else if(TAB==='etf'){h=bear+`<p class="sub">成交量足夠的 ETF（依成交金額排序），每檔都有建議進場價、停損、目標價，以及配息頻率和「為配息買值不值得」。槓桿 / 反向型只適合短線，不適合長抱。</p>
    <div class="filters"><input placeholder="搜尋 ETF 代號或名稱" value="${EQ}" oninput="EQ=this.value.trim();fillEtf()">
    <select onchange="EK=this.value;fillEtf()">${['','股票型','債券','槓桿/反向'].map(v=>`<option value="${v}" ${v===EK?'selected':''}>${v||'全部種類'}</option>`).join('')}</select>
    <select onchange="EF=this.value;fillEtf()">${['','月配','雙月配','季配','半年配','年配'].map(v=>`<option value="${v}" ${v===EF?'selected':''}>${v||'全部配息頻率'}</option>`).join('')}</select></div>
    <div class="stocks" id="elist"></div>`}
  else if(TAB==='divs'){const D=R.divs||[],cnt=k=>D.filter(r=>r[3]===k).length;
    h=`<p class="sub">依「多久配一次息」分類，可以挑每個月都有錢進來的組合（例如 3 檔不同月份的季配息）。「判斷」綜合了殖利率、有沒有填息、配息有沒有縮水、股價趨勢和公司體質。</p>
    <div class="chips">${['月配','雙月配','季配','半年配','年配',''].map(k=>`<button class="tab ${DF===k?'on':''}" onclick="DF='${k}';render()">${k||'全部'}（${k?cnt(k):D.length}）</button>`).join('')}</div>
    <div class="filters"><input placeholder="搜尋代號或名稱" value="${DQ}" oninput="DQ=this.value.trim();fillDiv()">
    <select onchange="DM=this.value;fillDiv()"><option value="">全部除息月份</option>${[1,2,3,4,5,6,7,8,9,10,11,12].map(m=>`<option value="${m}" ${String(m)===DM?'selected':''}>${m} 月有配息</option>`).join('')}</select>
    <select onchange="DT=this.value;fillDiv()">${['','ETF','股票','特別股','REIT'].map(v=>`<option value="${v}" ${v===DT?'selected':''}>${v||'全部種類'}</option>`).join('')}</select>
    <select onchange="DS=this.value;fillDiv()">${[['score','值得買程度'],['yld','殖利率高到低'],['fill','填息率高到低'],['next','即將除息']].map(o=>`<option value="${o[0]}" ${o[0]===DS?'selected':''}>${o[1]}</option>`).join('')}</select></div>
    <div class="card tblwrap" id="dlist"></div>
    <div class="mut" style="font-size:12px;margin-top:8px">年化殖利率＝最近幾次配息平均 × 一年配幾次 ÷ 現在股價。填息＝除息後股價漲回除息前的價格；沒填息代表領到的股息被股價下跌吃掉。以上依過去紀錄計算，未來配息可能改變。</div>`}
  else if(TAB==='nolimit'){const L=R.nolimit||[],cnt=k=>L.filter(r=>r.kind===k).length;
    h=`<div class="status down" style="margin-bottom:10px;color:var(--bad)">⚠️ 沒有漲跌幅限制的股票，一天可能漲或跌超過 10%（甚至 30%、50%），風險比一般股票大很多，一定要設停損、只用小錢。</div>
    <p class="sub">一般台股一天最多漲跌 10%，但下面這些沒有限制：剛上市櫃前 5 天的新股、追蹤國外市場的 ETF / ETN、債券 ETF，以及暫停後恢復交易的股票。</p>
    <div class="chips">${['','新股','其他','海外ETF','海外ETN','債券ETF'].map(k=>`<button class="tab ${NK===k?'on':''}" onclick="NK='${k}';render()">${k||'全部'}（${k?cnt(k):L.length}）</button>`).join('')}</div>
    <div class="stocks">${L.filter(r=>!NK||r.kind===NK).slice(0,150).map(nlCard).join('')||'<div class=mut>今天沒有這一類的股票</div>'}</div>`}
  else if(TAB==='all'){const inds=[...new Set(R.all.map(r=>r[3]).filter(Boolean))].sort();
    h=`<p class="sub">今日所有上市櫃股票（${R.all.length} 檔），點任一檔可看公司資料、EPS、股利與分析師評等。</p>
    <div class="filters"><input id="fq" placeholder="搜尋代號或名稱" value="${AQ}" oninput="AQ=this.value.trim();AN=100;fillAll()">
    <select id="fi" onchange="AI=this.value;AN=100;fillAll()"><option value="">全部產業</option>${inds.map(i=>`<option ${i===AI?'selected':''}>${i}</option>`).join('')}</select>
    <select id="fv" onchange="AV=this.value;AN=100;fillAll()">${['','實力股','有實力但短線過熱','中性觀察','題材投機','疑似炒作','體質偏弱','ETF','特別股','ETN','REIT','TDR'].map(v=>`<option value="${v}" ${v===AV?'selected':''}>${v||'全部鑑定'}</option>`).join('')}</select>
    <select id="fg" onchange="AGR=this.value;AN=100;fillAll()">${['','A','B','C','D','E'].map(v=>`<option value="${v}" ${v===AGR?'selected':''}>${v?'總評 '+v:'全部總評'}</option>`).join('')}</select>
    <select id="fs" onchange="AS=this.value;fillAll()">${SORTS.map(o=>`<option value="${o[0]}" ${o[0]===AS?'selected':''}>${o[1]}</option>`).join('')}</select></div>
    <div class="card tblwrap" id="alist"></div>`}
  else{const C=[['代號',r=>r.code],['名稱',r=>r.name],['價格',priceCell],['漲跌',pctCell],['成交量(張)',r=>f(r.vol,0)]];
    h=`<div class="tbls"><div class="card"><h3>漲幅前十</h3>${table(R.gainers,C)}</div>
    <div class="card"><h3>跌幅前十</h3>${table(R.losers,C)}</div>
    <div class="card"><h3>成交值前十</h3>${table(R.by_value,[...C.slice(0,4),['成交值(億)',r=>f(r.value/1000,1)]])}</div>
    <div class="card"><h3>外資 5 日買超前十</h3>${table(R.foreign_buy,[...C.slice(0,4),['外資5日(張)',r=>'<span class=up>'+f(r.f5,0)+'</span>']])}</div></div>`}
  $('#panel').innerHTML=h;
  if(TAB==='all')fillAll();
}
function tabsHTML(tabs){return tabs.map(t=>`<button class="tab ${TAB===t[0]?'on':''}" onclick="TAB='${t[0]}';$('#panel').innerHTML='';render()">${t[1]}</button>`).join('')}
let AQ='',AI='',AS='chg',AN=100,AV='',AGR='';
let NK='';
function nlCard(r){
  const Lv=LIVE[r.code],p=Lv&&Lv.price?Lv.price:r.close,c=Lv&&Lv.chg_pct!=null?Lv.chg_pct:r.chg_pct,n=r.np,pl=r.plan;
  const head=`<div class="top"><div><span class="nm">${r.name}</span><span class="cd">${r.code}・${r.kind}</span>
    <div class="mut" style="font-size:12px;margin-top:2px">${r.why}</div>
    ${r.upcoming?'<div style="margin-top:4px"><b>第一天不建議追，先看開盤後走勢</b></div>':`<div style="margin-top:4px"><b class="${(n||r).ac}">${(n||r).act}</b></div>`}</div>
    <div class="price"><div class="p ${cls(c)}">${f(p)}</div>${c!=null?`<div class="${cls(c)}">${sg(c)}${f(c)}%</div>`:'<div class="mut" style="font-size:12px">參考價</div>'}</div></div>`;
  let body='';
  if(r.upcoming)body=`<div style="font-size:13px;line-height:1.7">🕘 <b>何時進場：</b>前 1～2 天波動最大，等成交量變小、股價不再創新低時再考慮<br>🕐 <b>何時出場：</b>買進後跌破買價 10% 一定要停損；第 5 天收盤後恢復漲跌幅限制</div>`;
  else if(n)body=`<div class="plan"><div><small>止穩進場</small><b class="up">${f(n.lo)}~${f(Math.min(n.close,n.hi))}</b></div><div><small>停損</small><b class="down">${f(n.stop)}</b></div>
      <div><small>目標一</small><b>${f(n.t1)}</b></div><div><small>目標二</small><b>${f(n.t2)}</b></div></div>
    <div style="font-size:13px;line-height:1.7">🕘 <b>何時進場：</b>${n.entry}<br>🕐 <b>何時出場：</b>${n.exit}</div>
    <div class="mut" style="font-size:12px">已交易 ${n.days} 天｜首日開盤 ${f(n.first)}｜至今 ${sg(n.gain)}${f(n.gain,1)}%｜最低 ${f(n.lo)}、最高 ${f(n.hi)}</div>`;
  else if(pl)body=`<div class="plan"><div><small>建議進場</small><b class="up">${f(pl.entry_lo)}~${f(pl.entry_hi)}</b></div><div><small>停損 (${pl.stop_pct}%)</small><b class="down">${f(pl.stop)}</b></div>
      <div><small>目標一 (+${pl.t1_pct}%)</small><b>${f(pl.t1)}</b></div><div><small>目標二</small><b>${f(pl.t2)}</b></div></div>
    <div style="font-size:13px;line-height:1.7">🕐 <b>何時出場：</b>${r.exit}</div>
    <div class="mut" style="font-size:12px">趨勢 ${pl.trend}｜風報比 ${pl.rr??'-'}｜20日 ${r.ret20!=null?sg(r.ret20)+f(r.ret20,1)+'%':'-'}</div>${pl.note?`<div class="mut" style="font-size:12px">${pl.note}</div>`:''}`;
  return `<div class="st ${r.in_detail?'click':''}" ${r.in_detail?`onclick="lookup('${r.code}')"`:''}>${head}${body}</div>`
}
let EQ='',EK='',EF='',DF='月配',DQ='',DM='',DT='',DS='score';
const vc=v=>({'值得買':'ok','可以考慮':'ok','普通':'warn','不建議只為配息買':'bad','不適合領息':'bad'})[v]||'';
function fillEtf(){const el=$('#elist');if(!el)return;
  const L=(R.etfs||[]).filter(r=>(!EQ||r.code.includes(EQ)||r.name.includes(EQ))&&(!EK||r.kind===EK)&&(!EF||r.freq===EF));
  el.innerHTML=L.map(r=>{const Lv=LIVE[r.code],p=Lv&&Lv.price?Lv.price:r.close,c=Lv&&Lv.chg_pct!=null?Lv.chg_pct:r.chg_pct,pl=r.plan;
    return `<div class="st click" onclick="lookup('${r.code}')"><div class="top"><div><span class="nm">${r.name}</span><span class="cd">${r.code}・${r.kind}</span>
      <div style="margin-top:4px"><b class="${r.ac}">${r.act}</b></div></div>
      <div class="price"><div class="p ${cls(c)}">${f(p)}</div><div class="${cls(c)}">${sg(c)}${f(c)}%</div><div class="mut" style="font-size:11px">20日 ${r.ret20!=null?sg(r.ret20)+f(r.ret20,1)+'%':'-'}</div></div></div>
      <div class="plan"><div><small>建議進場</small><b class="up">${f(pl.entry_lo)}~${f(pl.entry_hi)}</b></div><div><small>停損 (${pl.stop_pct}%)</small><b class="down">${f(pl.stop)}</b></div>
        <div><small>目標一 (+${pl.t1_pct}%)</small><b>${f(pl.t1)}</b></div><div><small>目標二</small><b>${f(pl.t2)}</b></div></div>
      <div class="mut" style="font-size:12px">趨勢 ${pl.trend}｜風報比 ${pl.rr??'-'}｜${r.freq?r.freq+(r.yield!=null?' 殖利率 '+f(r.yield)+'%':''):'近一年沒有配息'}
      ${r.dv?`｜領息判斷 <span class="vtag ${vc(r.dv)}">${r.dv}</span>`:''}</div>${pl.note?`<div class="mut" style="font-size:12px">${pl.note}</div>`:''}</div>`}).join('')||'<div class=mut>沒有符合的 ETF</div>'}
function fillDiv(){const el=$('#dlist');if(!el)return;
  let L=(R.divs||[]).filter(r=>(!DF||r[3]===DF)&&(!DQ||r[0].includes(DQ)||r[1].includes(DQ))&&(!DM||r[4].includes(+DM))&&(!DT||r[2]===DT));
  const k={score:r=>-(r[8]??-99),yld:r=>-(r[6]??0),fill:r=>-(r[7]??-1),next:r=>r[10]||'9'}[DS];L=L.slice().sort((a,b)=>{const x=k(a),y=k(b);return x<y?-1:x>y?1:0});
  const mo=m=>m.length>=12?'每個月':m.join('、')+' 月';
  el.innerHTML=`<table><tr><th>名稱</th><th>配息</th><th>殖利率</th><th>填息率</th><th>值不值得</th><th>下次除息</th></tr>
  ${L.slice(0,300).map(r=>`<tr class="click" onclick="lookup('${r[0]}')"><td><b>${r[1]}</b><br><small class="mut">${r[0]}・${r[2]}・${f(r[11])}</small></td>
    <td>${r[3]}<br><small class="mut">${mo(r[4])}・最近 ${r[5]} 元</small></td>
    <td class="${r[6]>=6?'up':''}">${r[6]!=null?f(r[6])+'%':'-'}</td><td>${r[7]!=null?r[7]+'%':'-'}</td><td><span class="vtag ${vc(r[9])}">${r[9]}</span></td><td>${r[10]?r[10].slice(5):'-'}</td></tr>`).join('')}</table>
  ${L.length?(L.length>300?'<div class="mut" style="padding:8px">只顯示前 300 檔，請用搜尋或篩選</div>':''):'<div class="mut" style="padding:10px">沒有符合的股票</div>'}`}
const SORTS=[['chg','漲幅由高到低'],['chgd','跌幅由高到低'],['vol','成交量由大到小'],['total','分析師總評分'],['str','真實力分數'],['hype','炒作風險由高到低'],
  ['pe','本益比由低到高'],['yld','殖利率由高到低'],['grow','營收成長由高到低'],['gm','毛利率由高到低'],['r20','20日漲幅由高到低'],['mcap','市值由大到小'],['code','依代號']];
const NV=x=>x==null?-1e9:x;
function fillAll(){
  let rows=R.all.filter(r=>(!AQ||r[0].includes(AQ)||r[1].includes(AQ))&&(!AI||r[3]===AI)&&(!AV||r[7]===AV)&&(!AGR||r[16]===AGR));
  const key={chg:r=>-r[5],chgd:r=>r[5],vol:r=>-r[6],code:r=>r[0],total:r=>-NV(r[15]),str:r=>-NV(r[17]),hype:r=>-NV(r[18]),
    pe:r=>r[9]==null||r[9]<=0?1e9:r[9],yld:r=>-NV(r[10]),grow:r=>-NV(r[11]),gm:r=>-NV(r[12]),r20:r=>-NV(r[14]),mcap:r=>-NV(r[13])}[AS];
  rows.sort((a,b)=>{const x=key(a),y=key(b);return x<y?-1:x>y?1:0});
  const n=rows.length;rows=rows.slice(0,AN);
  $('#alist').innerHTML=`<table><tr><th>代號</th><th>名稱</th><th>產業</th><th>價格</th><th>漲跌</th><th>總評</th><th>鑑定</th><th>本益比</th><th>殖利率</th><th>營收年增</th><th>毛利率</th><th>成交量(張)</th></tr>${rows.map(r=>{
    const L=LIVE[r[0]],p=L&&L.price?L.price:r[4],c=L&&L.chg_pct!=null?L.chg_pct:r[5];
    return `<tr class="click" onclick="lookup('${r[0]}')"><td>${r[0]}</td><td>${r[1]}</td><td class="mut" style="text-align:left">${r[3]||r[2]}</td><td>${f(p)}</td><td class="${cls(c)}">${sg(c)}${f(c)}%</td><td><span class="gr g${r[16]}">${r[16]||'-'}</span></td><td><span class="vtag ${r[8]||''}">${r[7]||'-'}</span></td>
      <td>${r[9]!=null?f(r[9],1):'-'}</td><td>${r[10]!=null?f(r[10])+'%':'-'}</td><td class="${cls(r[11])}">${r[11]!=null?f(r[11],1)+'%':'-'}</td><td>${r[12]!=null?f(r[12],1)+'%':'-'}</td><td>${f(r[6],0)}</td></tr>`}).join('')}</table>
    ${n>AN?`<button class="g more" onclick="AN+=200;fillAll()">顯示更多（還有 ${n-AN} 檔）</button>`:`<div class="mut" style="margin-top:8px">共 ${n} 檔</div>`}`;
}

function liveCodes(){const s=new Set(['t00','o00']);
  [...R.momentum,...R.potential].forEach(x=>s.add(x.code));getWatch().forEach(c=>s.add(c));
  if(TAB==='rank')[...R.gainers,...R.losers,...R.by_value,...R.foreign_buy].forEach(x=>s.add(x.code));return[...s]}
let liveTimer=null,firstLive=true;
async function pollLive(once){
  clearTimeout(liveTimer);
  if(S){$('#refbtn').hidden=true}
  if(S&&!NATIVE){LIVE=Object.assign({},S.live);render();
    $('#livetxt').textContent='更新於 '+S.generated;
    if(SITE&&inSession()){checkAlerts(true);liveTimer=setTimeout(()=>{if($('#modal').style.display!=='flex'&&$('#chat').hidden)location.reload();else pollLive()},10*60000)}
    return}
  const on=inSession();
  if(on||firstLive||once){
    try{const d=await (await api('/api/live?codes='+liveCodes().join(',')));
      // 只採用不比分析資料日舊的報價
      for(const k in d){if(d[k].d>=R.date.replace(/-/g,'')||on)LIVE[k]=d[k]}
      render();checkAlerts();}catch(e){}
    firstLive=false;
  }
  $('#dot').className='live-dot'+(on?' on':'');
  $('#livetxt').textContent=on?'盤中即時 · 每 15 秒更新':'非交易時段（顯示收盤資料）';
  if(!once)liveTimer=setTimeout(pollLive,on?15000:60000);
}

async function lookup(code){
  code=code||$('#q').value.trim();if(!code)return;
  const d=await (await api('/api/stock?code='+encodeURIComponent(code)));
  if(d.error){$('#mbox').innerHTML=`<p>${d.error}</p><button class="g" onclick="closeModal()">關閉</button>`;$('#modal').style.display='flex';return}
  try{const l=await (await api('/api/live?codes='+d.code));if(l[d.code])LIVE[d.code]=l[d.code]}catch(e){}
  CUR=d;$('#mbox').innerHTML=detailHTML(d);
  $('#modal').style.display='flex';detailLive(d.code);
}
const li=a=>(a||[]).map(x=>'<li>'+x+'</li>').join('');
function cardPanel(d){
  const c=d.card;if(!c)return'';
  return `<div class="verdict"><div style="display:flex;align-items:center;gap:12px"><span class="gr bigg g${c.grade}">${c.grade}</span>
    <div><div class="mut" style="font-size:12px">分析師總評（${c.items.length} 面向加權）</div><b style="font-size:18px">${c.total} 分</b></div></div>
    <div class="card8">${c.items.map(x=>`<div class="c8"><span>${x[0]}</span><span class="gr g${x[2]}">${x[2]}</span>
      <div><i><b style="width:${x[1]??0}%"></b></i><div class="mut" style="font-size:11.5px;margin-top:2px">${x[3]}</div></div></div>`).join('')}</div></div>`
}
function kchart(d){
  const D=d.ohlc||[];if(D.length<5)return'<div class="mut">資料不足</div>';
  const n=D.length,dates=(R.dates||[]).slice(-n),W=420,H=220,VH=60,L=4,Rr=50,cw=(W-L-Rr)/n;
  const cl=D.map(x=>x[3]),ma=(k)=>cl.map((_,i)=>i<k-1?null:cl.slice(i-k+1,i+1).reduce((a,b)=>a+b,0)/k);
  const pl=d.plan||{},lv=[pl.stop,pl.t1,pl.entry_lo,pl.entry_hi].filter(x=>x);
  let hi=Math.max(...D.map(x=>x[1]),...lv),lo=Math.min(...D.map(x=>x[2]),...lv);const pad=(hi-lo)*0.05;hi+=pad;lo-=pad;
  const y=v=>8+(hi-v)/(hi-lo)*(H-16),vmax=Math.max(...D.map(x=>x[4]))||1,X=i=>L+i*cw+cw/2;
  let g='';
  for(let k=0;k<=4;k++){const v=lo+(hi-lo)*k/4;g+=`<line x1="${L}" x2="${W-Rr}" y1="${y(v)}" y2="${y(v)}" stroke="var(--line)" stroke-width="0.6"/><text x="${W-Rr+4}" y="${y(v)+4}" font-size="11" fill="var(--mut)">${f(v,v>=100?0:2)}</text>`}
  if(pl.entry_lo&&pl.entry_hi)g+=`<rect x="${L}" width="${W-L-Rr}" y="${y(pl.entry_hi)}" height="${Math.max(2,y(pl.entry_lo)-y(pl.entry_hi))}" fill="var(--up)" opacity="0.10"/>`;
  [[pl.stop,'var(--down)','停損'],[pl.t1,'var(--acc)','目標']].forEach(([v,c,t])=>{if(v)g+=`<line x1="${L}" x2="${W-Rr}" y1="${y(v)}" y2="${y(v)}" stroke="${c}" stroke-dasharray="4 3" stroke-width="1"/><text x="${L+4}" y="${y(v)-3}" font-size="11" fill="${c}">${t} ${f(v)}</text>`});
  D.forEach((x,i)=>{const up=x[3]>=x[0],c=up?'var(--up)':'var(--down)',bx=X(i),bw=Math.max(1.5,cw*0.65);
    g+=`<line x1="${bx}" x2="${bx}" y1="${y(x[1])}" y2="${y(x[2])}" stroke="${c}" stroke-width="1"/>`;
    g+=`<rect x="${bx-bw/2}" y="${y(Math.max(x[0],x[3]))}" width="${bw}" height="${Math.max(1,Math.abs(y(x[0])-y(x[3])))}" fill="${c}"/>`;
    const vh=x[4]/vmax*(VH-10);g+=`<rect x="${bx-bw/2}" y="${H+VH-vh}" width="${bw}" height="${vh}" fill="${c}" opacity="0.55"/>`});
  [[5,'#f5b942'],[20,'#4ea1ff'],[60,'#c084fc']].forEach(([k,c])=>{const m=ma(k);const pts=m.map((v,i)=>v==null?null:`${X(i).toFixed(1)},${y(v).toFixed(1)}`).filter(Boolean);
    if(pts.length>1)g+=`<polyline fill="none" stroke="${c}" stroke-width="1.3" points="${pts.join(' ')}"/>`});
  [0,Math.floor(n/2),n-1].forEach(i=>{if(dates[i])g+=`<text x="${X(i)}" y="${H+VH+14}" font-size="11" text-anchor="middle" fill="var(--mut)">${dates[i]}</text>`});
  return `<svg class="chart" viewBox="0 0 ${W} ${H+VH+20}" role="img" aria-label="K線圖">${g}</svg>
    <div class="legend"><span><b style="background:#f5b942"></b>5日線</span><span><b style="background:#4ea1ff"></b>月線(20日)</span><span><b style="background:#c084fc"></b>季線(60日)</span><span>紅K漲・綠K跌・淡紅區＝建議進場區</span></div>`
}
const kv2=a=>`<div class="kv">${a.map(x=>`<div>${x[0]}<b class="${x[2]||''}">${x[1]}</b></div>`).join('')}</div>`;
function patSection(d){
  const p=d.pat;if(!p)return'';const ic={good:'✓',bad:'✗',warn:'!'},cc={good:'ok',bad:'bad',warn:'warn'};
  return `<div class="sec"><h3>量價型態與風險</h3>${kv2([['相對大盤(20日)',p.rs!=null?sg(p.rs)+f(p.rs,1)+'%':'-',cls(p.rs)],['年化波動度',yi(p.vol,'%')],['60日最大回檔',yi(p.mdd,'%'),'down']])}
    <ul class="checks" style="margin-top:8px">${p.signals.length?p.signals.map(s=>`<li><b class="c-${cc[s[0]]}">${ic[s[0]]}</b><span>${s[1]}</span></li>`).join(''):'<li><b>・</b><span>近 5 日沒有明顯的主力進出貨型態</span></li>'}</ul>
    <div class="mut" style="font-size:12px;margin-top:6px">相對大盤＝個股 20 日漲幅減大盤 20 日漲幅；波動度越高代表股價越不穩。</div></div>`
}
function insiderSection(d){
  const h=d.fh||{};
  return `<div class="sec"><h3>董監、大股東與法人持股</h3>${kv2([['董監持股比例',yi(h.dir_hold,'%')],['董監質押比例',yi(h.dir_pledge,'%'),h.dir_pledge>=30?'c-bad':''],['外資持股比例',yi(h.foreign,'%')],
    ['借券賣出餘額',h.sbl!=null?f(h.sbl,0)+' 張':'-'],['借券占股本',yi(h.sbl_pct,'%')],['庫藏股',h.treasury?'有':'無']])}
    ${h.bigh&&h.bigh.length?`<div style="margin-top:8px;font-size:12.5px">持股逾 10% 大股東：${h.bigh.join('、')}</div>`:''}
    ${h.ins&&h.ins.length?`<h4>內部人申報轉讓（賣股）</h4>${h.ins.map(x=>`<div class="evt">${x[0]}｜${x[1]} ${x[2]}｜預定轉讓 ${f(x[3],0)} 張（${x[4]}）</div>`).join('')}`:''}
    <div class="mut" style="font-size:12px;margin-top:6px">董監持股高、質押低，代表經營者與股東站在同一邊；質押過高時股價下跌可能引發斷頭賣壓。</div></div>`
}
function finSection(d){
  const h=d.fh||{};
  return `<div class="sec"><h3>財報體質</h3>${kv2([['毛利率',yi(h.gm,'%')],['營業利益率',yi(h.om,'%')],['ROE(年化)',yi(h.roe,'%'),cls(h.roe)],['ROA(年化)',yi(h.roa,'%')],
    ['負債比',yi(h.debt,'%')],['流動比',h.cur!=null?f(h.cur,0)+'%':'-'],['每股淨值',yi(h.bvps,' 元')],['股價淨值比',d.fund&&d.fund.pb?f(d.fund.pb)+' 倍':'-']])}
    <div class="mut" style="font-size:12px;margin-top:6px">ROE 大於 15% 屬優秀；一般產業負債比低於 50%、流動比高於 150% 較穩健（金融業負債比本來就高）。</div></div>`
}
function eventSection(d){
  const h=d.fh||{};if(!(h.mat&&h.mat.length)&&!(h.viol&&h.viol.length))return'';
  return `<div class="sec"><h3>重大訊息與違規紀錄</h3>${(h.viol||[]).map(x=>`<div class="evt" style="color:var(--bad)">⚠ ${x[0]} 違規裁罰 ${x[2]||''} 萬：${x[1]}</div>`).join('')}
    ${(h.mat||[]).map(x=>`<div class="evt">${x[0]}｜${x[1]}</div>`).join('')}</div>`
}
function peerSection(d){
  const ind=(d.fund||{}).ind;if(!ind)return'';
  const rows=R.all.filter(r=>r[3]===ind).sort((a,b)=>NV(b[13])-NV(a[13])).slice(0,8);
  if(!rows.find(r=>r[0]===d.code)){const me=R.all.find(r=>r[0]===d.code);if(me)rows.push(me)}
  return `<div class="sec"><h3>同業比較（${ind}，依市值）</h3><div class="tblwrap"><table><tr><th>代號</th><th>名稱</th><th>總評</th><th>鑑定</th><th>市值(億)</th><th>本益比</th><th>殖利率</th><th>營收年增</th><th>毛利率</th><th>20日漲幅</th></tr>
    ${rows.map(r=>`<tr class="click" onclick="lookup('${r[0]}')" style="${r[0]===d.code?'background:var(--card2);font-weight:700':''}"><td>${r[0]}</td><td>${r[1]}</td><td><span class="gr g${r[16]}">${r[16]||'-'}</span></td>
      <td><span class="vtag ${r[8]||''}">${r[7]}</span></td><td>${r[13]!=null?f(r[13],0):'-'}</td><td>${r[9]!=null?f(r[9],1):'-'}</td><td>${r[10]!=null?f(r[10])+'%':'-'}</td>
      <td class="${cls(r[11])}">${r[11]!=null?f(r[11],1)+'%':'-'}</td><td>${r[12]!=null?f(r[12],1)+'%':'-'}</td><td class="${cls(r[14])}">${r[14]!=null?f(r[14],1)+'%':'-'}</td></tr>`).join('')}</table></div></div>`
}
function nolimSection(d){return d.nolim?`<div class="status down" style="margin:8px 0;color:var(--bad)">🚀 無漲跌幅限制：${d.nolim}。一天可能漲跌超過 10%，請嚴設停損。</div>`:''}
function divSection(d){
  const v=d.dv;if(!v)return'';const ic={ok:'✓',bad:'✗',warn:'!'};
  if(!v.events.length)return `<div class="sec"><h3>配息分析</h3><div><span class="vtag ${vc(v.verdict)}">${v.verdict}</span></div><ul class="checks">${v.why.map(c=>`<li><b class="c-${c[0]}">${ic[c[0]]}</b><span>${c[1]}</span></li>`).join('')}</ul>${v.next?`<div>下次除息 ${v.next.date}${v.next.cash?'，'+v.next.cash+' 元':''}</div>`:''}</div>`;
  return `<div class="sec"><h3>配息分析：為了領息買值不值得？</h3>
    <div style="font-size:15px;margin-bottom:6px"><b>${v.freq}</b>（${v.months.join('、')} 月除息）　判斷 <span class="vtag ${vc(v.verdict)}" style="font-size:16px">${v.verdict}</span> <span class="mut">${v.score} 分</span></div>
    ${kv2([['最近一次配息',v.last+' 元'],['預估一年配息',f(v.est,3)+' 元'],['年化殖利率',v.yield!=null?f(v.yield)+'%':'-',v.yield>=6?'up':''],['近 12 個月實配',f(v.ttm,3)+' 元'],
      ['填息率',v.fill_rate!=null?v.fill_rate+'%':'-'],['下次除息',v.next?v.next.date.slice(5)+'（'+v.next.cash+' 元）':'尚未公告']])}
    <ul class="checks">${v.why.map(c=>`<li><b class="c-${c[0]}">${ic[c[0]]}</b><span>${c[1]}</span></li>`).join('')}</ul>
    ${v.fills&&v.fills.length?`<div class="tblwrap"><table><tr><th>除息日</th><th>配息</th><th>除息前價格</th><th>填息</th></tr>${v.fills.slice().reverse().map(x=>`<tr><td>${x.date}</td><td>${x.cash}</td><td>${f(x.pre)}</td><td class="${x.filled?'up':'down'}">${x.filled?(x.days?x.days+' 天填息':'已填息'):'尚未填息'}</td></tr>`).join('')}</table></div>`:''}
    <div class="mut" style="font-size:12px;margin-top:6px">配息會從股價扣掉（除息），要等股價漲回來（填息）才算真的賺到。只看殖利率高就買，可能賺了股息賠了價差。</div></div>`
}
function dtSection(d){
  const t=d.dt;if(!t)return'';
  const st=!t.listed?'<b class="down">不可現股當沖</b>':t.dispose?'<b class="down">處置中，當沖受限制</b>':t.susp?'<b>只能先買後賣</b>（暫停先賣後買）':'<b class="up">可以雙向現股當沖</b>';
  return `<div class="sec"><h3>當沖資訊</h3><div style="font-size:14px">${st}</div>${kv2([['昨日當沖比',t.ratio!=null?f(t.ratio,1)+'%':'-',t.ratio>=35?'c-warn':''],['平均波動',yi(t.atr_pct,'%')],['樞紐 PP',f(t.pp)],
    ['壓力 R1',f(t.r1),'up'],['壓力 R2',f(t.r2),'up'],['支撐 S1',f(t.s1),'down'],['支撐 S2',f(t.s2),'down']])}
    ${t.plan?'<h3 style="margin-top:12px">今日當沖計畫</h3>'+dtPlan(Object.assign({code:d.code},t)):''}
    <div class="mut" style="font-size:12px;margin-top:6px">樞紐點用昨天的最高、最低、收盤計算：站上 PP 偏多、跌破 PP 偏空。當沖風險很高，新手請先在股票小學堂練習。</div></div>`
}
function dtLive(r,p){
  const L=LIVE[r.code],n=new Date(),m=n.getHours()*60+n.getMinutes(),wd=n.getDay()>0&&n.getDay()<6;
  if(!wd||m<8*60+30||m>13*60+35)return `<div class="mut" style="font-size:12px">⏰ 開盤後（9:00～13:30）這裡會顯示即時提示</div>`;
  if(m<9*60+15)return `<div class="status">⏳ 現在 ${n.getHours()}:${String(n.getMinutes()).padStart(2,'0')}，開盤前 15 分鐘波動最亂，先觀察高低點，9:15 以後再決定</div>`;
  if(m>=13*60+20)return `<div class="status down">🔔 已經 13:20，手上有當沖部位的請馬上平倉，不要留到收盤</div>`;
  if(!L||!L.price)return `<div class="mut" style="font-size:12px">（需要 App 或電腦版才有即時價）</div>`;
  const x=L.price,long=p.side==='多';let t,c='';
  if(long?x<=p.stop:x>=p.stop){t='❌ 已碰到停損價 '+f(p.stop)+'，有部位要出場；沒部位今天先不做';c='down'}
  else if(long?x>=p.t2:x<=p.t2){t='🎯 已到第二目標 '+f(p.t2)+'，全部出場';c='up'}
  else if(long?x>=p.t1:x<=p.t1){t='✅ 已到第一目標 '+f(p.t1)+'，先'+(long?'賣':'回補')+'一半，停損移到進場價';c='up'}
  else if(long?x>=p.entry:x<=p.entry){const hi=L.h,lo=L.l;t=(long?'👀 站在進場價之上，':'👀 在進場價之下，')+'看有沒有'+(long?'突破今天高點 '+f(hi):'跌破今天低點 '+f(lo))+'，有就可以進場'}
  else t='⌛ 還沒到進場價 '+f(p.entry)+'，耐心等';
  return `<div class="status ${c}">即時 ${f(x)}：${t}</div>`
}
function dtPlan(r){
  const p=r.plan;if(!p)return'';const col=p.side==='多'?'up':'down';
  return `<div style="font-size:13px;margin-top:6px;line-height:1.7">
    <div><b class="${col}">${p.side==='多'?'📈':'📉'} ${p.title}</b>${p.rr!=null?`　風報比 <b class="${p.rr>=1.5?'up':''}">${f(p.rr,1)}</b>`:''}</div>
    <div>🕘 <b>何時進場：</b>${p.when}</div>
    <div>💰 <b>進場價：</b>約 <b>${f(p.entry)}</b>　🛑 <b>停損：</b><b class="down">${f(p.stop)}</b></div>
    <div>🎯 <b>出場目標：</b>第一 <b class="up">${f(p.t1)}</b>、第二 <b class="up">${f(p.t2)}</b></div>
    <div>🕐 <b>何時出場：</b>${p.exit}；最晚 <b>${p.last}</b> 一定要${p.side==='多'?'賣出':'買回'}</div>
    <div class="mut">🚫 ${p.skip}</div>${dtLive(r,p)}</div>`
}
function verdictPanel(d){
  const v=d.sv;if(!v)return'';const ic={ok:'✓',bad:'✗',warn:'!'};
  const desc={'實力股':'基本面紮實、交易正常，股價有業績支撐。','有實力但短線過熱':'公司本身有實力，但近期漲太快或交易過熱，宜等回檔。',
    '疑似炒作':'多項交易異常訊號，股價可能由短線資金或題材推動，風險高。','題材投機':'有部分投機訊號，需確認業績能否跟上。',
    '體質偏弱':'基本面條件不足，暫時沒有明顯炒作，但也缺乏上漲理由。','中性觀察':'實力與風險都不突出，持續觀察。'}[v.verdict]||'';
  return `<div class="verdict"><div><span class="mut">實力 vs 炒作鑑定</span><div class="big"><span class="vtag ${v.vc}" style="font-size:18px">${v.verdict}</span></div>
    <div style="font-size:13px;margin-top:4px">${desc}</div></div>
    ${v.strength==null?'':`<div class="meter"><span>真實力</span><i><b style="width:${v.strength}%;background:var(--good)"></b></i><span>${v.strength}</span></div>
    <div class="meter"><span>炒作風險</span><i><b style="width:${v.hype}%;background:var(--bad)"></b></i><span>${v.hype}</span></div>`}
    <ul class="checks">${v.checks.map(c=>`<li><b class="c-${c[0]}">${ic[c[0]]}</b><span>${c[1]}</span></li>`).join('')}</ul></div>`
}
function chipSection(d){
  const c=d.chip2||{};if(!Object.keys(c).length)return'';
  const kv=a=>`<div class="kv">${a.map(x=>`<div>${x[0]}<b class="${x[2]||''}">${x[1]}</b></div>`).join('')}</div>`;
  const fl=(c.flags||[]).map(x=>`<div class="status down" style="margin-top:6px;color:var(--bad)">⚠ ${x[0]}股：${x[1]}</div>`).join('')+(c.tv?`<div class="status" style="margin-top:6px;color:var(--bad)">⚠ 被列入證交所「投資理財節目異常推介個股」</div>`:'');
  return `<div class="sec"><h3>籌碼結構（主力 / 散戶）</h3>${kv([
    ['市值',c.mcap!=null?f(c.mcap,1)+' 億':'-'],['當日週轉率',yi(c.turnover,'%')],['當沖比',yi(c.daytrade,'%'),c.daytrade>=35?'c-warn':''],
    ['千張大戶持股',yi(c.big1000,'%')],['400張以上大戶',yi(c.big400,'%')],['50張以下散戶',yi(c.retail,'%')],
    ['股東人數',c.holders?f(c.holders,0)+' 人':'-'],['大戶週變化',c.big1000_chg!=null?sg(c.big1000_chg)+f(c.big1000_chg)+'%':'累積中',cls(c.big1000_chg)],['股東人數週變化',c.holders_chg!=null?sg(c.holders_chg)+f(c.holders_chg,0):'累積中'],
    ['融資餘額',c.margin!=null?f(c.margin,0)+' 張':'-'],['融資增減',c.margin_chg!=null?sg(c.margin_chg)+f(c.margin_chg,0)+' 張':'-',cls(c.margin_chg)],['融資使用率',yi(c.margin_use,'%')],
    ['融券餘額',c.short!=null?f(c.short,0)+' 張':'-'],['券資比',yi(c.short_ratio,'%')],[c.margin_chg_n?`近${c.margin_chg_n[0]}日融資`:'多日融資變化',c.margin_chg_n?sg(c.margin_chg_n[1])+f(c.margin_chg_n[1],0)+' 張':'累積中']])}
    ${fl}<div class="mut" style="font-size:12px;margin-top:6px">集保資料日 ${c.tdcc_date||'-'}（每週更新）。大戶比例上升、股東人數下降代表籌碼集中；融資大增而法人賣出，常見於散戶追高。</div></div>`
}
const yi=(x,u='')=>x==null?'-':f(x)+u;
function detailHTML(d){
  const F=d.fund||{},P=d.prof||{},E=d.rep||{},D=F.div||{},M=F.mrev,pl=d.plan,ai=!!(window.claude&&window.claude.use);
  const kv=(a)=>`<div class="kv">${a.map(x=>`<div>${x[0]}<b class="${x[2]||''}">${x[1]}</b></div>`).join('')}</div>`;
  return `<div style="display:flex;justify-content:space-between;gap:8px"><div><h2 style="margin:0">${d.name} <span class=mut>${d.code}</span></h2>
    <div class="mut">${d.market}・${F.ind||'—'}・趨勢 <b class="${pl.trend==='多頭'?'up':pl.trend==='空頭'?'down':''}">${pl.trend}</b></div></div>
    <button class="g" onclick="closeModal()" aria-label="關閉">✕</button></div>
  <div class="sec" style="border:0;padding-top:4px"><span class="rating ${E.rc}">${E.rating}</span>
    ${E.target?`合理價 <b>${f(E.target)}</b>（<span class="${cls(E.upside)}">${sg(E.upside)}${E.upside}%</span>）`:'<span class=mut>無法以本益比估算合理價</span>'}
    <div class="summary">${E.summary}</div>${cardPanel(d)}${verdictPanel(d)}</div>
  <div class="sec"><h3>K 線圖（近 60 日）</h3>${kchart(d)}</div>
  ${liveSecHTML(d)}
  ${nolimSection(d)}${divSection(d)}${dtSection(d)}
  ${stockCard(d)}
  ${(d.news&&d.news.length)?`<div class="sec"><h3>近期新聞</h3><div class="news">${newsItems(d.news)}</div></div>`:''}
  <div class="sec"><h3>分析師觀點</h3>
    <h4>基本面</h4><ul>${li(E.fund)||'<li>無財報資料</li>'}</ul>
    <h4>技術面</h4><ul>${li(E.tech)}</ul><h4>籌碼面</h4><ul>${li(E.chip)}</ul>
    <h4>風險提示</h4><ul>${li(E.risks)}</ul></div>
  ${ai?`<div class="sec"><h3>AI 分析師深度報告</h3><div class="mut" style="font-size:12px">由 Claude 依上方資料撰寫公司業務、產業前景與投資建議（約 30 秒）</div>
    <div id="aibox" class="ai"><button class="b" style="margin-top:8px" onclick="aiReport()">產生 AI 研究報告</button></div></div>`:''}
  ${patSection(d)}
  ${chipSection(d)}
  ${d.etf?'':insiderSection(d)+finSection(d)+eventSection(d)+peerSection(d)}
  ${d.etf?`<div class="sec"><h3>${d.stype||'ETF'} 說明</h3><p style="font-size:13.5px;line-height:1.8">${({'ETF':'ETF 是「一籃子股票」：買一張就等於同時買了很多家公司，所以沒有單一公司的財報和 EPS。挑 ETF 主要看：追蹤什麼指數、內扣費用、配息和是否有溢價。','特別股':'特別股通常每年發固定股息，價格波動比普通股小，但沒有投票權，公司可能在幾年後收回。','ETN':'ETN 是券商發行、追蹤某個指數的商品，有到期日，也要承擔發行券商的信用風險。','REIT':'REIT（不動產投資信託）把大樓租金收入分給投資人，配息穩定，但會受利率和房市影響。','TDR':'TDR 是外國公司在台灣上市的存託憑證，股價會受原本國家股價與匯率影響。'})[d.stype]||''}${/^00.*[LR]$/.test(d.code)?'<br><b class="down">這是槓桿或反向型 ETF</b>，每天會重新平衡，長期持有會有耗損，只適合短線。':''}</p></div>`:`<div class="sec"><h3>公司資料</h3>${kv([['公司全名',P.full||'-'],['產業',F.ind||'-'],['董事長',P.chair||'-'],['總經理',P.gm||'-'],
    ['成立日期',P.found||'-'],['上市櫃日期',P.listed||'-'],['資本額',P.cap?f(P.cap)+' 億':'-'],['發行股數',P.shares?f(P.shares)+' 億股':'-'],
    ['英文簡稱',P.en||'-']])}${P.web?`<div style="margin-top:8px;font-size:12px">公司網站：<a href="${P.web}" target="_blank" rel="noopener" style="color:var(--blue)">${P.web}</a></div>`:''}</div>
  <div class="sec"><h3>獲利與評價</h3>${kv([
    [F.eps_q?`${F.eps_y} 前${F.eps_q}季 EPS`:'累計 EPS',yi(F.eps_cum,' 元'),cls(F.eps_cum)],['全年化 EPS',yi(F.eps_est,' 元')],['近四季 EPS',yi(F.eps_ttm,' 元')],
    ['營業利益率',yi(F.op_margin,'%')],['稅後淨利率',yi(F.net_margin,'%')],['本益比',yi(F.pe,' 倍')],
    ['同業本益比',yi(F.ind_pe,' 倍')],['股價淨值比',yi(F.pb,' 倍')],['配股後 EPS',F.eps_after_stock!=null?f(F.eps_after_stock)+' 元':'無配股']])}</div>
  ${M?`<div class="sec"><h3>月營收（${M.ym}）</h3>${kv([['單月營收',f(M.rev/1e5)+' 億'],['月增率',yi(M.mom,'%'),cls(M.mom)],['年增率',yi(M.yoy,'%'),cls(M.yoy)],
    ['今年累計',f(M.cum/1e5)+' 億'],['累計年增',yi(M.cum_yoy,'%'),cls(M.cum_yoy)]])}${M.note?`<div class="mut" style="margin-top:6px;font-size:12px">公司說明：${M.note}</div>`:''}</div>`:''}`}
  <div class="sec"><h3>股利政策${D.year?`（${D.year} 年度）`:''}</h3>${kv([['現金股利',D.cash!=null?f(D.cash,2)+' 元':'無資料'],['股票股利（配股）',D.stock?f(D.stock,2)+' 元':'無'],
    ['現金殖利率',yi(D.yield,'%')],['盈餘配發率',F.payout!=null?F.payout+'%':'-'],['配股後 EPS',F.eps_after_stock!=null?f(F.eps_after_stock)+' 元':'-'],['除權息參考價',yi(D.ref_price)]])}
    ${D.rows&&D.rows.length?`<div class="tblwrap" style="margin-top:8px"><table><tr><th>期間</th><th>進度</th><th>現金(元)</th><th>配股(元)</th></tr>${D.rows.map(r=>`<tr><td>${r.period}</td><td>${r.status}</td><td>${f(r.cash,2)}</td><td>${f(r.stock,2)}</td></tr>`).join('')}</table></div>`:''}
    ${D.ex?`<div class="status up" style="margin-top:8px">📅 即將${D.ex.type}：${D.ex.date}${D.ex.cash?'，現金 '+f(D.ex.cash,2)+' 元':''}${D.ex.stock_ratio?'，每股配 '+D.ex.stock_ratio+' 股':''}</div>`:''}
    <div class="mut" style="font-size:12px;margin-top:6px">配股後 EPS = 全年化 EPS ÷ (1 + 股票股利/10)；除權息參考價 = (股價 − 現金股利) ÷ (1 + 股票股利/10)</div></div>
  <div class="sec"><h3>技術指標</h3>${kv([['5日均',f(d.ma5)],['10日均',f(d.ma10)],['月線',f(d.ma20)],['季線',f(d.ma60)],['K / D',f(d.k,0)+' / '+f(d.d,0)],['ATR',f(d.atr)],
    ['5日漲跌',f(d.ret5)+'%',cls(d.ret5)],['20日漲跌',f(d.ret20)+'%',cls(d.ret20)],['60日高',f(d.high60)],['外資10日',f(d.f10,0),cls(d.f10)],['投信10日',f(d.t10,0),cls(d.t10)],['RSI',f(d.rsi,0)]])}</div>`;
}
function md(t){
  const esc=t.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
  let out='',inl=false;
  for(let l of esc.split('\n')){
    l=l.replace(/\*\*(.+?)\*\*/g,'<b>$1</b>');
    if(/^\s*[-*•]\s+/.test(l)){if(!inl){out+='<ul>';inl=true}out+='<li>'+l.replace(/^\s*[-*•]\s+/,'')+'</li>';continue}
    if(inl){out+='</ul>';inl=false}
    if(/^#+\s/.test(l))out+='<h4>'+l.replace(/^#+\s/,'')+'</h4>';else if(l.trim())out+='<p style="margin:4px 0">'+l+'</p>';
  }
  return out+(inl?'</ul>':'');
}
async function aiReport(){
  const box=$('#aibox'),d=CUR;let sample=null;
  try{sample=await window.claude.use('sample')}catch(e){}
  if(!sample){box.textContent='此網頁目前無法使用 AI 功能（需在 Claude 開啟並允許）。';return}
  box.innerHTML='<span class="mut">AI 分析師撰寫中…</span>';
  const data={股票:d.name+' '+d.code,市場:d.market,產業:d.fund.ind,公司:d.prof,收盤價:d.close,資料日:d.date,
    技術面:{月線:d.ma20,季線:d.ma60,RSI:d.rsi,'5日漲跌%':d.ret5,'20日漲跌%':d.ret20,'60日高':d.high60,趨勢:d.plan.trend},
    籌碼:{外資10日張:d.f10,投信10日張:d.t10},基本面:d.fund,籌碼結構:d.chip2,財報與董監:d.fh,量價型態:d.pat,評分卡:d.card,實力炒作鑑定:d.sv,近期新聞:d.news,規則評等:{評等:d.rep.rating,合理價:d.rep.target},建議進出場:d.plan};
  const prompt=`你是台灣券商的資深股票分析師。請用繁體中文，為以下這檔台股撰寫一份專業但易懂的研究報告（約 600～800 字），使用以下段落標題（以 ## 開頭）：
## 公司簡介與主要業務（主要產品、營收來源、主要客戶或應用領域）
## 產業地位與前景（產業趨勢、競爭優勢、成長動能）
## 營運與財務解讀（根據提供的 EPS、營收、利潤率資料）
## 股利政策（現金股利、配股、殖利率、配股後 EPS 的意義）
## 技術面與籌碼面
## 是真實力還是炒作（根據實力炒作鑑定、籌碼結構、注意/處置紀錄、當沖比、融資變化、新聞判斷，給出明確結論）
## 投資建議（評等、合理價區間、進場與停損策略）
## 主要風險
規則：數字只能使用下方提供的資料，不要編造財報數字；公司業務與產業背景可依一般公開知識撰寫，若不確定請說明。結尾加一句「本報告僅供參考，不構成投資建議」。
資料：${JSON.stringify(data)}`;
  try{const r=await sample(prompt,{modelTier:'default',onText:({text})=>{box.innerHTML=md(text)}});box.innerHTML=md(r.text)}
  catch(e){box.innerHTML=`<span class="mut">${e&&e.code==='not_granted'?'未允許此網頁使用 AI，可在網頁權限中開啟。':e&&e.code==='rate_limited'?'使用太頻繁，請稍後再試。':'AI 報告產生失敗，請稍後再試。'}</span>`}
}
$('#q').addEventListener('keydown',e=>{if(e.key==='Enter')lookup()});
async function refreshData(){await api('/api/refresh');$('#app').style.display='none';$('#loading').style.display='block';
  WATCH_DATA={};await new Promise(r=>setTimeout(r,800));await boot();await loadWatch();render()}
/* ============================== 橘橘：原創橘白貓吉祥物 */
let MY_PIC=(()=>{try{return localStorage.getItem('tw_mascot')}catch(e){return null}})();
const CAT = {"teacher": "data:image/jpeg;base64,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", "happy": "data:image/jpeg;base64,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", "wow": "data:image/jpeg;base64,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", "think": "data:image/jpeg;base64,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", "oops": "data:image/jpeg;base64,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", "t_table": "data:image/jpeg;base64,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", "t_half": "data:image/jpeg;base64,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", "t_detective": "data:image/jpeg;base64,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", "t_cool": "data:image/jpeg;base64,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", "t_bakery": "data:image/jpeg;base64,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", "t_birthday": "data:image/jpeg;base64,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", "t_sake": "data:image/jpeg;base64,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", "t_grid": "data:image/jpeg;base64,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"};
function niu(mood = 'happy', cls = '') {
  if (MY_PIC) return `<img src="${MY_PIC}" alt="老師" class="${cls}" style="width:100%;height:100%;object-fit:cover;border-radius:50%">`;
  const k = {happy: 'teacher', joy: 'happy', wow: 'wow', think: 'think', oops: 'oops'}[mood] || 'teacher';
  return `<img src="${CAT[k]}" alt="橘橘老師" class="${cls}" style="width:100%;height:100%;object-fit:cover;border-radius:50%;border:3px solid #ffc23c;box-sizing:border-box;background:#fff">`;
}
/* ============================== 即時五檔與盤中走勢（電腦版） */
const INTRA={};let DTIMER=null;
function closeModal(){$('#modal').style.display='none';clearTimeout(DTIMER);DTIMER=null}
function liveSecHTML(d){
  if(S&&!NATIVE)return `<div class="sec"><h3>即時買賣量（五檔）</h3><div class="mut" style="font-size:13px">${SITE?'網站版盤中每 30 分鐘更新一次報價快照。要每 10 秒更新的五檔與盤中走勢，請用 Android App 或電腦版。':'手機雲端版無法連線證交所即時報價（盤中每小時檢查一次你的自選股並推播提醒）。要每 15 秒更新的五檔與盤中走勢，請用電腦版。'}</div></div>`;
  return `<div class="sec" id="livesec"><h3>即時買賣量（五檔）與盤中走勢</h3><div id="livebox" class="mut">連線中…</div></div>`;
}
function renderLiveBox(code){
  const L=LIVE[code],box=$('#livebox');if(!box)return;
  if(!L||!L.bids){box.innerHTML='<span class="mut">目前沒有即時資料（非交易時段或連線失敗）。</span>';return}
  const mx=Math.max(1,...L.bids.map(x=>x[1]),...L.asks.map(x=>x[1]));
  const row=(x,c)=>`<tr><td class="${c}">${f(x[0])}</td><td>${f(x[1],0)}<span class="vbar" style="width:${x[1]/mx*36}px;background:var(--${c==='up'?'up':'down'})"></span></td></tr>`;
  const bsum=L.bids.reduce((a,x)=>a+x[1],0),asum=L.asks.reduce((a,x)=>a+x[1],0);
  const pts=INTRA[code]||[];let chart='';
  if(pts.length>1){const ps=pts.map(x=>x[1]),hi=Math.max(...ps,L.y||ps[0]),lo=Math.min(...ps,L.y||ps[0]),W=360,H=110,X=i=>i/(pts.length-1)*(W-10)+5,Y=v=>8+(hi-v)/((hi-lo)||1)*(H-16);
    chart=`<svg class="chart" viewBox="0 0 ${W} ${H}"><line x1="0" x2="${W}" y1="${Y(L.y)}" y2="${Y(L.y)}" stroke="var(--mut)" stroke-dasharray="4 3"/><polyline fill="none" stroke="${L.price>=L.y?'var(--up)':'var(--down)'}" stroke-width="2" points="${pts.map((x,i)=>X(i).toFixed(1)+','+Y(x[1]).toFixed(1)).join(' ')}"/><text x="6" y="14" font-size="11" fill="var(--mut)">今日盤中（開著網頁時記錄，${pts[0][0]}～${pts[pts.length-1][0]}）</text></svg>`}
  box.innerHTML=`<div style="display:flex;gap:12px;flex-wrap:wrap;align-items:baseline"><b style="font-size:20px" class="${cls(L.chg_pct)}">${f(L.price)}</b><span class="${cls(L.chg_pct)}">${sg(L.chg_pct)}${f(L.chg_pct)}%</span>
    <span class="mut">${L.time||''}・總量 ${f(L.v,0)} 張・單量 ${f(L.tv,0)} 張</span></div>
    <div class="five" style="margin-top:6px"><div><b class="down">委賣（賣方）</b><table>${[...L.asks].reverse().map(x=>row(x,'down')).join('')}</table></div><div><b class="up">委買（買方）</b><table>${L.bids.map(x=>row(x,'up')).join('')}</table></div></div>
    <div class="mut" style="font-size:12.5px;margin-top:4px">五檔委買 ${f(bsum,0)} 張 / 委賣 ${f(asum,0)} 張：${bsum>asum*1.3?'買方掛單較多，承接力道強':asum>bsum*1.3?'賣方掛單較多，上方賣壓重':'買賣力道接近'}</div>${chart}`;
}
async function detailLive(code){
  clearTimeout(DTIMER);if((S&&!NATIVE)||!$('#livebox')||$('#modal').style.display==='none')return;
  try{const d=await api('/api/live?codes='+code);if(d[code]){LIVE[code]=d[code];const L=d[code];if(inSession()&&L.price){(INTRA[code]=INTRA[code]||[]).push([L.time||'',L.price]);if(INTRA[code].length>600)INTRA[code].shift()}}}catch(e){}
  renderLiveBox(code);checkAlerts();
  DTIMER=setTimeout(()=>detailLive(code),inSession()?10000:60000);
}
/* ============================== 買賣點提醒 */
let DB=null,ALERTS=[];
const todayKey=()=>new Date().toISOString().slice(0,10);
function planOf(code){const x=WATCH_DATA[code]||[...R.momentum,...R.potential].find(s=>s.code===code);if(!x)return null;const h=getHold()[code],p={name:x.name,...x.plan};if(h)p.stop=myStop(x,h);return p}
function alertCodes(){return [...new Set([...getWatch(),...R.momentum.map(x=>x.code),...R.potential.map(x=>x.code)])]}
function judgeLive(code,price){const p=planOf(code);if(!p||!price)return null;
  if(p.trend==='空頭'&&price<p.entry_lo&&!getHold()[code])return null;
  if(price<=p.stop)return{type:'stop',msg:`${p.name} 跌到 ${f(price)}，跌破停損 ${f(p.stop)}，持有的話該賣出停損`};
  if(price>=p.t2)return{type:'t2',msg:`${p.name} 漲到 ${f(price)}，達到第二目標 ${f(p.t2)}，可以獲利出場`};
  if(price>=p.t1)return{type:'t1',msg:`${p.name} 漲到 ${f(price)}，達到第一目標 ${f(p.t1)}，可以先賣一半`};
  if(price>=p.entry_lo&&price<=p.entry_hi)return{type:'buy',msg:`${p.name} 現在 ${f(price)}，進入建議買進區 ${f(p.entry_lo)}~${f(p.entry_hi)}，可以考慮分批買進`};
  return null}
function checkAlerts(force){
  if((S&&!NATIVE&&!force)||!inSession())return;
  const seen=JSON.parse(localStorage.getItem('tw_alert_seen')||'{}');
  alertCodes().forEach(c=>{const L=LIVE[c];if(!L)return;const a=judgeLive(c,L.price);if(!a)return;const k=todayKey()+c+a.type;if(seen[k])return;seen[k]=1;
    pushAlert({code:c,ts:Date.now(),time:L.time,...a})});
  try{localStorage.setItem('tw_alert_seen',JSON.stringify(seen))}catch(e){}
}
function pushAlert(a){
  ALERTS.unshift(a);ALERTS=ALERTS.slice(0,30);
  toast(a.msg,a.type==='buy'?'joy':a.type==='stop'?'oops':'wow');
  try{if(NATIVE)NATIVE.notify('橘橘提醒：'+(a.type==='buy'?'可以買了':a.type==='stop'?'該停損了':'可以賣了'),a.msg)}catch(e){}
  try{if(!NATIVE&&window.Notification&&Notification.permission==='granted')new Notification('橘橘提醒：'+(a.type==='buy'?'可以買了':a.type==='stop'?'該停損了':'可以賣了'),{body:a.msg})}catch(e){}
  beep();$('#catbadge').hidden=false;
}
function beep(){try{const ac=new (window.AudioContext||window.webkitAudioContext)(),o=ac.createOscillator(),g=ac.createGain();o.frequency.value=880;o.connect(g);g.connect(ac.destination);g.gain.setValueAtTime(.15,ac.currentTime);o.start();o.stop(ac.currentTime+.25)}catch(e){}}
function toast(msg,mood){const t=document.createElement('div');t.className='toast';t.innerHTML=niu(mood||'happy')+`<div>${msg}</div>`;document.body.appendChild(t);setTimeout(()=>t.remove(),8000)}
function showAlerts(){
  $('#catbadge').hidden=true;
  const how=NATIVE?`<p>Android App：開著 App 時每 15 秒檢查；App 關掉後，盤中每 15 分鐘在背景檢查你的<b>自選股</b>，到買點、目標價或停損價時跳出手機通知。</p>`:
    SITE?`<p>網站版：盤中開著網頁時，每 30 分鐘用最新報價檢查自選股和推薦股，到點時在網頁上提醒。想在手機背景收到通知，請用 Android App。</p>`:S?`<p>手機雲端版：盤中（9:17~13:17 每小時）橘橘會檢查你的<b>自選股</b>，到買點或賣點時推播通知到你的手機（Claude App 需開啟通知）。請先在個股頁按「☆ 加入自選」。</p>`:
    `<p>電腦版：盤中每 15 秒檢查自選股和今日推薦股，到買點、目標價或停損價時跳出提醒並發出聲音。</p><button class="b" onclick="askNotify()">開啟桌面通知</button>`;
  $('#mbox').innerHTML=`<div style="display:flex;justify-content:space-between"><h2 style="margin:0">🔔 買賣提醒</h2><button class="g" onclick="closeModal()">✕</button></div>${how}
    <h3>最近的提醒</h3><div class="alertlist">${ALERTS.length?ALERTS.map(a=>`<div><b>${a.time||new Date(a.ts).toLocaleString('zh-TW')}</b>　${a.msg}</div>`).join(''):'<div class="mut">目前還沒有提醒</div>'}</div>
    <h3>正在監控的股票</h3><div class="mut" style="font-size:13px">${alertCodes().map(c=>{const p=planOf(c);return p?`${p.name}（買 ${f(p.entry_lo)}~${f(p.entry_hi)}／停損 ${f(p.stop)}／目標 ${f(p.t1)}）`:''}).filter(Boolean).join('<br>')}</div>`;
  $('#modal').style.display='flex';
}
async function askNotify(){try{const r=await Notification.requestPermission();toast(r==='granted'?'已開啟桌面通知！':'沒有開啟通知，仍會在網頁上提醒你。')}catch(e){toast('這個瀏覽器不支援桌面通知')}}
/* 雲端版：自選股與提醒存在雲端資料庫，讓盤中排程可以讀取 */
async function initDB(){
  if(!S||!window.claude||!window.claude.use)return;
  try{DB=await window.claude.use('db')}catch(e){DB=null}if(!DB)return;
  try{const snap=await DB.collection('watch').get();const codes=snap.docs.map(d=>d.id);if(codes.length){const w=[...new Set([...getWatch(),...codes])];setWatch(w);await loadWatch();render()}}catch(e){}
  try{DB.doc('alerts/latest').onSnapshot(s=>{if(!s.exists)return;const items=(s.data().items||[]);ALERTS=items;const last=+localStorage.getItem('tw_alert_last')||0;
    if(items[0]&&items[0].ts>last){toast(items[0].msg,'wow');$('#catbadge').hidden=false;try{localStorage.setItem('tw_alert_last',items[0].ts)}catch(e){}}},()=>{})}catch(e){}
}
async function syncWatchDB(code,on){
  if(!DB)return;
  try{if(on){const d=WATCH_DATA[code]||await api('/api/stock?code='+code);await DB.doc('watch/'+code).set({code,name:d.name,market:d.market,entry_lo:d.plan.entry_lo,entry_hi:d.plan.entry_hi,stop:d.plan.stop,t1:d.plan.t1,t2:d.plan.t2,date:R.date,added:Date.now()})}
    else await DB.doc('watch/'+code).delete()}catch(e){toast('自選股雲端同步失敗，提醒可能收不到')}
}
/* ============================== 換成自己的吉祥物圖片（只存在這台裝置） */
function drawCats(){$('#logoCat').innerHTML=niu('happy');$('#catface').innerHTML=niu('happy');$('#chatcat').innerHTML=niu('happy')}
function showPic(msg){
  $('#mbox').innerHTML=`<div style="display:flex;justify-content:space-between"><h2 style="margin:0">🐱 換吉祥物圖片</h2><button class="g" onclick="closeModal()">✕</button></div>
    <p>選一張你自己的圖片，取代右下角和標題的橘橘。圖片只存在<b>這台裝置的瀏覽器</b>，不會上傳。請使用你有權使用的圖片。</p>
    <div style="display:grid;gap:12px;justify-items:start"><div style="width:120px;height:120px">${niu('happy')}</div>
    <label class="b" for="picIn" style="cursor:pointer;padding:8px 14px;border-radius:8px;background:var(--blue);color:var(--onacc);font-weight:700">選擇圖片</label><input id="picIn" type="file" accept="image/*" hidden onchange="setPic(this.files[0])">
    ${MY_PIC?'<button class="g" onclick="clearPic()">換回橘橘</button>':''}<div class="mut">${msg||''}</div></div>`;
  $('#modal').style.display='flex';
}
function setPic(file){
  if(!file)return;const r=new FileReader();
  r.onload=()=>{const img=new Image();img.onload=()=>{const n=256,c=document.createElement('canvas');c.width=c.height=n;const g=c.getContext('2d'),k=Math.min(n/img.width,n/img.height);
      g.drawImage(img,(n-img.width*k)/2,(n-img.height*k)/2,img.width*k,img.height*k);MY_PIC=c.toDataURL('image/png');let ok=true;
      try{localStorage.setItem('tw_mascot',MY_PIC)}catch(e){ok=false}drawCats();showPic(ok?'換好了！':'這個瀏覽器無法儲存圖片，關掉網頁後會換回橘橘。')};
    img.onerror=()=>showPic('讀不到這張圖片，請換一張 PNG 或 JPG。');img.src=r.result};
  r.readAsDataURL(file);
}
function clearPic(){MY_PIC=null;try{localStorage.removeItem('tw_mascot')}catch(e){}drawCats();showPic('已換回橘橘。')}
/* ============================== 橘橘分析師對話 */
let CHAT=[],SAMPLE=null;
(async()=>{try{if(window.claude&&window.claude.use)SAMPLE=await window.claude.use('sample')}catch(e){}})();
function toggleChat(){const c=$('#chat');c.hidden=!c.hidden;$('#catbub').hidden=true;$('#catbadge').hidden=true;if(!c.hidden){if(!CHAT.length)botSay(`喵～我是<b>橘橘分析師</b>！打股票名稱或代號問我，例如「台積電可以買嗎？」「2317 什麼時候賣？」「今天大盤怎麼樣？」`,'happy');renderChips();setTimeout(()=>$('#chatq').focus(),50)}}
function renderChips(){const picks=[...R.momentum.slice(0,2),...R.potential.slice(0,1)].map(x=>x.name);$('#chips').innerHTML=['今天大盤怎麼樣？',...picks.map(n=>n+'可以買嗎？'),'推薦哪一檔？'].map(q=>`<button onclick="$('#chatq').value='${q}';sendChat()">${q}</button>`).join('')}
function addMsg(html,who){const m=document.createElement('div');m.className='m '+who;m.innerHTML=html;$('#msgs').appendChild(m);$('#msgs').scrollTop=1e9;return m}
function botSay(html,mood){return addMsg(html,'bot')}
function findStock(text){
  const code=(text.match(/\b(\d{4})\b/)||[])[1];if(code&&R.all.find(r=>r[0]===code))return code;
  let best=null;R.all.forEach(r=>{if(r[1]&&text.includes(r[1].replace(/-KY|\*|-創/g,''))&&(!best||r[1].length>best[1].length))best=r});return best?best[0]:null;
}
function decide(d){
  const L=LIVE[d.code],price=L&&L.price?L.price:d.close,pl=d.plan,rt=(d.rep||{}).rating,v=(d.sv||{}).verdict;
  if(v==='疑似炒作')return['❌ 不建議買','炒作警訊很多，股價可能被短線資金拉抬。','oops'];
  if(price<=pl.stop)return['❌ 先不要買',`價格 ${f(price)} 已在停損價 ${f(pl.stop)} 之下，走勢偏弱。`,'oops'];
  if(pl.trend==='空頭')return['⏳ 先觀望',`目前是空頭，等站回月線 ${f(d.ma20)} 再考慮。`,'think'];
  if(price>=pl.entry_lo&&price<=pl.entry_hi&&['買進','逢低布局'].includes(rt))return['✅ 可以考慮分批買進',`現在 ${f(price)} 在建議買進區 ${f(pl.entry_lo)}~${f(pl.entry_hi)} 內。`,'happy'];
  if(price>pl.entry_hi)return['⏳ 價格偏高，等拉回',`現在 ${f(price)} 高於建議區，等回到 ${f(pl.entry_hi)} 以下再買比較安全。`,'think'];
  if(price<pl.entry_lo)return['👀 觀察中',`現在 ${f(price)} 低於建議區，要確認能守住 ${f(pl.stop)}。`,'think'];
  return['🤔 中性，可以小量或觀望',`評等「${rt}」，條件普通。`,'think'];
}
function ruleReply(d){
  const [dec,why]=decide(d),pl=d.plan,E=d.rep||{},v=d.sv||{},c=d.card||{};
  const bad=(v.checks||[]).filter(x=>x[0]!=='ok').slice(0,2).map(x=>x[1]),good=(v.checks||[]).filter(x=>x[0]==='ok').slice(0,2).map(x=>x[1]);
  return `<div class="dec">${dec}</div>${why}<ul><li>總評 <b>${c.grade||'-'}</b>（${c.total??'-'} 分）・鑑定 <b>${v.verdict||'-'}</b>・評等 <b>${E.rating||'-'}</b>${E.target?`・合理價 ${f(E.target)}`:''}</li>
    <li>建議買進 <b class="up">${f(pl.entry_lo)}~${f(pl.entry_hi)}</b>・停損 <b class="down">${f(pl.stop)}</b>・目標 ${f(pl.t1)} / ${f(pl.t2)}</li>
    <li>已經持有：跌破 ${f(pl.stop)} 就停損；漲到 ${f(pl.t1)} 可以先賣一半。</li>
    ${good.map(x=>`<li>👍 ${x}</li>`).join('')}${bad.map(x=>`<li>⚠️ ${x}</li>`).join('')}</ul>
    <button class="g" onclick="lookup('${d.code}')">看 ${d.name} 完整分析</button>`;
}
function marketReply(){
  const m=R.market,top=R.momentum.slice(0,3).map(x=>`${x.name}（${x.sv?x.sv.verdict:''}）`).join('、')||'今天沒有符合條件的強勢股';
  return `<div class="dec">大盤：${m.mood||'-'}</div>加權指數 ${f(m.taiex)}（${sg(m.taiex_chg_pct)}${f(m.taiex_chg_pct)}%），${m.position||''}。<br>今日推薦：${top}。${R.news&&R.news.market?'<br>📰 '+R.news.market:''}`;
}
async function sendChat(){
  const q=$('#chatq').value.trim();if(!q)return;$('#chatq').value='';addMsg(q.replace(/</g,'&lt;'),'me');CHAT.push({role:'user',content:q});
  const code=findStock(q);let d=null,html;
  if(code){d=await api('/api/stock?code='+code);if(d.error)d=null}
  if(d){try{const l=await api('/api/live?codes='+d.code);if(l[d.code])LIVE[d.code]=l[d.code]}catch(e){} html=`<b>${d.name}（${d.code}）</b><br>`+ruleReply(d)}
  else if(/大盤|今天|市場|行情|指數/.test(q))html=marketReply();
  else if(/推薦|哪一檔|買什麼|哪支/.test(q))html=`今天橘橘推薦：<ul>${R.momentum.slice(0,5).map(x=>`<li><a href="#" onclick="event.preventDefault();lookup('${x.code}')">${x.name} ${x.code}</a>：買 ${f(x.plan.entry_lo)}~${f(x.plan.entry_hi)}，停損 ${f(x.plan.stop)}${x.sv?'・'+x.sv.verdict:''}</li>`).join('')}</ul>大盤是「${R.market.mood}」，${R.market.position}`;
  else html='我還沒找到你說的股票喵～請輸入股票<b>名稱</b>或 4 碼<b>代號</b>，例如「鴻海」或「2317」。';
  botSay(html);
  if(SAMPLE){const box=botSay('<span class="mut">橘橘正在深入分析…</span>');
    const data=d?{股票:d.name+' '+d.code,現價:LIVE[d.code]?LIVE[d.code].price:d.close,資料日:d.date,建議:d.plan,評等:d.rep,鑑定:d.sv,評分卡:d.card,基本面:d.fund,財報與董監:d.fh,籌碼:d.chip2,量價型態:d.pat,新聞:d.news}
      :{大盤:R.market,新聞:R.news,今日推薦:R.momentum.slice(0,5).map(x=>({名稱:x.name,代號:x.code,建議:x.plan,鑑定:x.sv}))};
    const hist=CHAT.slice(-6).map(m=>(m.role==='user'?'使用者：':'橘橘：')+m.content).join('\n');
    const prompt=`你是「橘橘」，一隻活潑可愛、說話專業又易懂的橘白貓台股分析師。用繁體中文回答，口語、親切，可以偶爾加「喵」，約 150~250 字。
規則：只能使用下面提供的資料裡的數字，不要編造；先給明確結論（能不能買／何時賣／要注意什麼），再說 2~3 個理由（基本面、技術面、籌碼或炒作風險），最後給具體價位（買進區、停損、目標）。結尾提醒「僅供參考，不構成投資建議」。
最近對話：\n${hist}\n資料：${JSON.stringify(data)}`;
    try{const r=await SAMPLE(prompt,{modelTier:'default',onText:({text})=>{box.innerHTML=text.replace(/</g,'&lt;').replace(/\*\*(.+?)\*\*/g,'<b>$1</b>').replace(/\n/g,'<br>');$('#msgs').scrollTop=1e9}});
      box.innerHTML=r.text.replace(/</g,'&lt;').replace(/\*\*(.+?)\*\*/g,'<b>$1</b>').replace(/\n/g,'<br>');CHAT.push({role:'assistant',content:r.text})}
    catch(e){box.innerHTML=`<span class="mut">${e&&e.code==='not_granted'?'（還沒允許 AI 功能，以上是橘橘的規則分析）':'（AI 暫時無法回答，以上是橘橘的規則分析）'}</span>`}}
}

drawCats();if(SITE||NATIVE)$('#schoollink').hidden=false;
setTimeout(()=>{const b=$('#catbub');if(b)b.hidden=true},9000);
boot().then(loadWatch).then(()=>{if(R){render();initDB()}});
</script>"""


def full_page():
    return ('<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"></head><body>'
            + PAGE + '</body></html>')


def auto_refresh_loop():
    """程式一直開著時，每天收盤資料出來後自動更新，不用手動按"""
    while True:
        time.sleep(600)
        try:
            if STATUS["state"] == "ready" and REPORT and candidate_dates()[0].strftime("%Y-%m-%d") > REPORT["date"]:
                print("偵測到新的交易日資料，自動更新…")
                safe_update()
        except Exception:
            traceback.print_exc()


def lan_ip():
    import socket
    try:
        sk = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sk.connect(("8.8.8.8", 80))
        ip = sk.getsockname()[0]
        sk.close()
        return ip
    except Exception:
        return None


def export_static(path):
    """產生單一 HTML 檔(資料內嵌)，給手機/雲端版使用"""
    update_data()
    if "--rss" in sys.argv and not NEWS:
        apply_rss_news()
        build_report_again()
    d = REPORT["date"]
    stocks = {}
    for code in HIST:
        if HIST[code]["dates"][-1] != d or len(HIST[code]["c"]) < 30:
            continue
        o = stock_detail(code)
        if o:
            stocks[code] = o
    codes = ["t00", "o00"] + [x["code"] for k in ("momentum", "potential", "gainers", "losers", "by_value", "foreign_buy")
                              for x in REPORT[k]]
    live = live_quotes(list(dict.fromkeys(codes)))
    report = {k: v for k, v in REPORT.items() if k != "names"}
    data = {"report": report, "stocks": stocks, "live": live,
            "generated": datetime.now().strftime("%m/%d %H:%M")}
    js = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    h2 = json.dumps(HIST2, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    html = PAGE.replace("<script>\nlet R=null", "<script>window.__TW_STATIC__=" + js + ";</script>\n<script>window.__TW_HIST2__=" + h2
                        + ";</script>\n<script>\nlet R=null", 1)
    assert "__TW_STATIC__" in html
    if "--site" in sys.argv:
        html = site_page(html)
    if arg("--lesson"):
        os.makedirs(os.path.dirname(arg("--lesson")) or ".", exist_ok=True)
        with open(arg("--lesson"), "w", encoding="utf-8") as fh:
            json.dump(build_daily_lesson(), fh, ensure_ascii=False, separators=(",", ":"))
        print("已輸出今日時事課", arg("--lesson"))
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    print(f"已輸出 {path} ({len(html) // 1024} KB)，資料日 {d}，共 {len(stocks)} 檔")


def arg(name):
    if name in sys.argv:
        i = sys.argv.index(name)
        return sys.argv[i + 1] if len(sys.argv) > i + 1 else ""
    return None


def load_cli_inputs():
    """--news news.json：雲端排程整理的新聞；--prev 舊網頁.html：取回上次的融資/集保歷史"""
    global NEWS, PREV_HIST2
    if arg("--news"):
        try:
            with open(arg("--news"), encoding="utf-8") as fh:
                NEWS = json.load(fh)
            print(f"已載入新聞：{len(NEWS.get('themes') or [])} 個題材、{len(NEWS.get('stocks') or {})} 檔個股新聞")
        except Exception as e:
            print("  ! 新聞檔讀取失敗", e)
    if arg("--prev"):
        try:
            import re
            with open(arg("--prev"), encoding="utf-8") as fh:
                html = fh.read()
            mt = re.search(r"window\.__TW_HIST2__=(.*?);</script>", html, re.S)
            if mt:
                PREV_HIST2 = json.loads(mt.group(1).replace("<\\/", "</"))
                print("已載入上次的融資 / 集保歷史")
        except Exception as e:
            print("  ! 上次網頁讀取失敗", e)


def fetch_rss_news():
    """沒有 Claude 時的新聞：抓 Yahoo 股市、MoneyDJ 的 RSS 標題"""
    import re
    import xml.etree.ElementTree as ET
    items = []
    for url, src in (("https://tw.stock.yahoo.com/rss?category=tw-market", "Yahoo股市"),
                     ("https://www.moneydj.com/KMDJ/RssCenter.aspx?svc=NR&fno=1&arg=MB010000", "MoneyDJ")):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=20, context=SSL_CTX) as r:
                root = ET.fromstring(r.read())
            for it in root.iter("item"):
                t = (it.findtext("title") or "").strip()
                link = (it.findtext("link") or "").strip()
                pub = it.findtext("pubDate") or ""
                m = re.search(r"(\d{1,2}) (\w{3}) (\d{4})", pub)
                if t and link.startswith("http"):
                    items.append({"title": t, "url": link, "source": src, "date": f"{m.group(2)} {m.group(1)}" if m else ""})
        except Exception as e:
            print("  ! RSS 下載失敗", src, e)
    seen, out = set(), []
    for x in items:
        if x["title"] not in seen:
            seen.add(x["title"]); out.append(x)
    return out


def apply_rss_news():
    global NEWS
    heads = fetch_rss_news()
    if not heads:
        return
    stocks = {}
    for code, p in HIST.items():
        nm = p["name"].replace("-KY", "").replace("*", "")
        if len(nm) < 2:
            continue
        hits = [h for h in heads if nm in h["title"]]
        if hits:
            stocks[code] = [{"title": h["title"], "source": h["source"], "date": h["date"], "sentiment": "新聞", "url": h["url"]} for h in hits[:3]]
    NEWS = {"date": datetime.now().strftime("%Y-%m-%d"), "headlines": heads[:12], "stocks": stocks}
    print(f"已抓取 RSS 新聞 {len(heads)} 則，對應到 {len(stocks)} 檔股票")


def build_daily_lesson():
    """股票小學堂「今日時事課」：用今天真實的盤勢挑出教學案例（不需要 Claude）"""
    d = REPORT["date"]
    latest = {c: analyze(c) for c, s in HIST.items() if s["dates"][-1] == d and len(s["c"]) >= 60}
    latest = {c: a for c, a in latest.items() if a}

    def series(code, n=60):
        s = HIST[code]
        k = min(n, len(s["c"]))
        return [[s["o"][i], s["h"][i], s["l"][i], s["c"][i], s["v"][i]] for i in range(len(s["c"]) - k, len(s["c"]))]

    cases = []
    m = REPORT["market"]
    up, down = REPORT["breadth"]["up"], REPORT["breadth"]["down"]
    chg = m.get("taiex_chg_pct") or 0
    market = {"title": f"大盤{'上漲' if chg >= 0 else '下跌'} {abs(chg):.2f}%，目前是「{m.get('mood', '-')}」",
              "explain": f"加權指數收 {m.get('taiex', 0):,.0f} 點。今天有 {up} 檔股票上漲、{down} 檔下跌。"
                         f"指數{'在' if (m.get('taiex') or 0) >= (m.get('ma20') or 0) else '跌破'}月線（{m.get('ma20', 0):,.0f}）{'之上' if (m.get('taiex') or 0) >= (m.get('ma20') or 0) else ''}，"
                         f"所以老師的建議是：{m.get('position', '')}。",
              "kid": ("今天全班考試，大部分同學分數都進步了，代表整體氣氛很好。" if up > down else
                      "今天全班考試，大部分同學分數都退步了，大家心情不太好，這時候要小心，不要急著買東西。")}
    # 1. 強勢突破
    for x in REPORT["momentum"][:5]:
        a = latest.get(x["code"])
        if a:
            cases.append({"tag": "成交量・趨勢", "lesson": 2, "title": f"{a['name']}：帶量上漲的強勢股", "code": a["code"], "name": a["name"], "ohlc": series(a["code"]),
                          "note": "今天", "explain": f"{a['name']}今天{'上漲' if a['chg_pct'] >= 0 else '下跌'} {abs(a['chg_pct'])}%，成交量是月均量的 {a['vol'] / a['vma20']:.1f} 倍。"
                          + "、".join(x["why"][:3]) + "。這就是課程裡說的「價漲量增」加上「多頭排列」。",
                          "kid": "就像排隊買冰淇淋的人突然變很多，而且價格也一直漲，代表很多人真的很想要。",
                          "quiz": {"q": f"{a['name']}今天價格上漲、成交量也放大，這叫做？", "o": ["價漲量增", "價跌量增", "價漲量縮", "量價背離"], "a": 0,
                                   "e": "價格漲、成交量也變大，代表買的人變多，是健康的上漲。"}})
            break
    # 2. 炒作警訊
    sus = sorted([a for a in latest.values() if sv_of(a)["verdict"] == "疑似炒作"], key=lambda a: -sv_of(a)["hype"])
    if sus:
        a = sus[0]; sv = sv_of(a)
        bad = [t for k, t in sv["checks"] if k != "ok"][:3]
        cases.append({"tag": "炒作股", "lesson": 9, "title": f"{a['name']}：炒作警訊很多的股票", "code": a["code"], "name": a["name"], "ohlc": series(a["code"]),
                      "note": "今天", "explain": f"{a['name']}近 20 天漲跌 {a['ret20']:+.0f}%，炒作風險 {sv['hype']} 分。" + "；".join(bad) + "。這種股票看起來很刺激，但很容易暴漲暴跌。",
                      "kid": "有人在班上一直喊「這張貼紙超稀有」，大家搶著買，價格被炒得很高。等很多人買了，喊的人就偷偷賣掉。",
                      "quiz": {"q": f"像{a['name']}這樣被列為注意或處置、又沒有業績支撐的股票，新手應該？", "o": ["趕快追進去", "先不要追，風險很高", "借錢買", "全部押下去"], "a": 1,
                               "e": "交易所會把交易異常的股票列為注意股或處置股，新手最好避開。"}})
    # 3. 大型股跌破月線
    big = sorted([a for a in latest.values() if not is_nonstock(a["code"]) and a["chg_pct"] <= -2 and a["ma20"] and a["close"] < a["ma20"] <= a["prev"] * 1.05],
                 key=lambda a: -(a["vma20"] or 0) * a["close"])
    if big:
        a = big[0]
        cases.append({"tag": "均線・支撐", "lesson": 3, "title": f"{a['name']}：跌破月線", "code": a["code"], "name": a["name"], "ohlc": series(a["code"]),
                      "note": "今天", "explain": f"{a['name']}今天下跌 {abs(a['chg_pct'])}%，收在 {a['close']}，跌破月線 {a['ma20']:.2f}。月線大約是最近一個月買進的人的平均成本，跌破代表很多人套牢，要小心賣壓。",
                      "kid": "全班最近 20 次考試的平均是 80 分，你這次只考 70 分，掉到平均以下了，要注意是不是狀況變差。",
                      "quiz": {"q": "股價跌破月線，代表什麼？", "o": ["最近買的人平均都賺錢", "最近一個月買的人平均套牢", "一定會漲停", "沒有意義"], "a": 1,
                               "e": "月線約等於近一個月的平均成本，跌破後容易有解套賣壓。"}})
    # 4. 實力股拉回
    good = sorted([a for a in latest.values() if sv_of(a)["verdict"] == "實力股" and a["ret5"] is not None and a["ret5"] < -3
                   and a["ma60"] and a["close"] > a["ma60"]], key=lambda a: -(a["vma20"] or 0) * a["close"])
    if good:
        a = good[0]
        cases.append({"tag": "停損停利・基本面", "lesson": 8, "title": f"{a['name']}：好公司拉回", "code": a["code"], "name": a["name"], "ohlc": series(a["code"]),
                      "note": "今天", "explain": f"{a['name']}被鑑定為「實力股」（實力 {sv_of(a)['strength']} 分），最近 5 天回檔 {abs(a['ret5']):.1f}%，但還在季線 {a['ma60']:.2f} 之上。"
                      "好公司回檔時，可以等它在支撐附近止穩再分批買，並先想好停損價。",
                      "kid": "你最喜歡的玩具今天打折了！但是先確認它沒有壞掉（公司還是很賺錢），再決定要不要買，而且不要一次把零用錢花光。",
                      "quiz": {"q": "好公司股價回檔時，比較好的做法是？", "o": ["一次全部買進", "等止穩、分批買，先想好停損", "趕快賣掉", "借錢加碼"], "a": 1,
                               "e": "分批買進、設好停損，可以降低看錯的風險。"}})
    heads = (NEWS.get("headlines") or [])[:6] if NEWS else []
    return {"date": d, "generated": datetime.now().strftime("%Y-%m-%d %H:%M"), "dates": DATES[-60:], "market": market, "cases": cases, "headlines": heads}


def site_page(html):
    """免費網站版：完整網頁 + 可加到手機主畫面 (PWA)"""
    head = ('<!doctype html><html lang="zh-Hant"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">'
            '<meta name="theme-color" content="#ffc23c"><meta name="apple-mobile-web-app-capable" content="yes">'
            '<meta name="apple-mobile-web-app-title" content="台股分析"><meta name="mobile-web-app-capable" content="yes">'
            '<link rel="manifest" href="manifest.webmanifest"><link rel="apple-touch-icon" href="icon-192.png">'
            '<link rel="icon" href="icon-192.png"></head><body>')
    tail = ('<script>if("serviceWorker" in navigator)navigator.serviceWorker.register("sw.js").catch(()=>{});</script>'
            '</body></html>')
    return head + html + tail


def write_picks(path):
    update_data()
    picks = [{"code": x["code"], "name": x["name"], "list": k} for k in ("momentum", "potential") for x in REPORT[k]]
    with open(path, "w", encoding="utf-8") as fh:
        json.dump({"date": REPORT["date"], "picks": picks,
                   "top_value": [{"code": x["code"], "name": x["name"]} for x in REPORT["by_value"]]}, fh, ensure_ascii=False, indent=1)
    print(f"已輸出 {path}：{len(picks)} 檔推薦/潛力股")


def main():
    load_cli_inputs()
    if arg("--picks") is not None:
        write_picks(arg("--picks") or "picks.json")
        return
    if "--export" in sys.argv:
        i = sys.argv.index("--export")
        export_static(sys.argv[i + 1] if len(sys.argv) > i + 1 else "tw_stock_report.html")
        return
    threading.Thread(target=safe_update, daemon=True).start()
    threading.Thread(target=auto_refresh_loop, daemon=True).start()
    try:
        srv = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    except OSError:
        print(f"連接埠 {PORT} 已被使用，可能程式已在執行中。直接開啟瀏覽器…")
        webbrowser.open(f"http://127.0.0.1:{PORT}")
        return
    url = f"http://127.0.0.1:{PORT}"
    print(f"儀表板網址: {url}  (關閉此視窗即結束程式)")
    ip = lan_ip()
    if ip:
        print(f"手機連同一個 Wi-Fi，用瀏覽器打開: http://{ip}:{PORT}  (Windows 若跳出防火牆詢問請按「允許」)")
    if "--no-browser" not in sys.argv:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()

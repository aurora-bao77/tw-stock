package tw.stock.app;

import android.app.job.JobInfo;
import android.app.job.JobParameters;
import android.app.job.JobScheduler;
import android.app.job.JobService;
import android.content.ComponentName;
import android.content.Context;
import android.content.SharedPreferences;

import org.json.JSONArray;
import org.json.JSONObject;

import java.net.URLEncoder;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.HashSet;
import java.util.Locale;
import java.util.Set;
import java.util.TimeZone;

/** App 關掉時，盤中每 15 分鐘檢查自選股是否到達買點 / 賣點 */
public class AlertJobService extends JobService {
    private static final int JOB_ID = 1;

    static void schedule(Context c) {
        JobScheduler js = c.getSystemService(JobScheduler.class);
        if (js == null || js.getPendingJob(JOB_ID) != null) return;
        js.schedule(new JobInfo.Builder(JOB_ID, new ComponentName(c, AlertJobService.class))
                .setPeriodic(15 * 60 * 1000L)
                .setRequiredNetworkType(JobInfo.NETWORK_TYPE_ANY)
                .setPersisted(true)
                .build());
    }

    @Override
    public boolean onStartJob(JobParameters params) {
        new Thread(() -> {
            try { check(getApplicationContext()); } catch (Exception ignored) { }
            jobFinished(params, false);
        }).start();
        return true;
    }

    @Override
    public boolean onStopJob(JobParameters params) { return true; }

    static void check(Context c) throws Exception {
        TimeZone tz = TimeZone.getTimeZone("Asia/Taipei");
        Calendar now = Calendar.getInstance(tz);
        int dow = now.get(Calendar.DAY_OF_WEEK), m = now.get(Calendar.HOUR_OF_DAY) * 60 + now.get(Calendar.MINUTE);
        if (dow == Calendar.SATURDAY || dow == Calendar.SUNDAY || m < 9 * 60 || m > 13 * 60 + 35) return;
        SharedPreferences sp = c.getSharedPreferences("tw", Context.MODE_PRIVATE);
        JSONArray watch = new JSONArray(sp.getString("watch", "[]"));
        if (watch.length() == 0) return;
        SimpleDateFormat df = new SimpleDateFormat("yyyyMMdd", Locale.US);
        df.setTimeZone(tz);
        String today = df.format(now.getTime());
        StringBuilder ch = new StringBuilder();
        for (int i = 0; i < watch.length(); i++) {
            JSONObject w = watch.getJSONObject(i);
            if (ch.length() > 0) ch.append('|');
            ch.append("上櫃".equals(w.optString("market")) ? "otc_" : "tse_").append(w.getString("code")).append(".tw");
        }
        String res = Net.get("https://mis.twse.com.tw/stock/api/getStockInfo.jsp?ex_ch=" + URLEncoder.encode(ch.toString(), "UTF-8")
                + "&json=1&delay=0&_=" + System.currentTimeMillis());
        JSONArray msgs = new JSONObject(res).optJSONArray("msgArray");
        if (msgs == null) return;
        Set<String> seen = new HashSet<>(sp.getStringSet("seen", new HashSet<>()));
        for (int i = 0; i < msgs.length(); i++) {
            JSONObject q = msgs.getJSONObject(i);
            if (!today.equals(q.optString("d"))) continue;
            double p = num(q.optString("z"));
            if (Double.isNaN(p)) p = num(q.optString("b").split("_")[0]);
            if (Double.isNaN(p)) continue;
            for (int j = 0; j < watch.length(); j++) {
                JSONObject w = watch.getJSONObject(j);
                if (!w.getString("code").equals(q.optString("c"))) continue;
                String type = null, msg = null, name = w.optString("name");
                if (p <= w.optDouble("stop")) { type = "stop"; msg = name + " 跌到 " + p + "，跌破停損 " + w.optDouble("stop") + "，持有的話該賣出停損"; }
                else if (p >= w.optDouble("t2")) { type = "t2"; msg = name + " 漲到 " + p + "，達到第二目標 " + w.optDouble("t2") + "，可以獲利出場"; }
                else if (p >= w.optDouble("t1")) { type = "t1"; msg = name + " 漲到 " + p + "，達到第一目標 " + w.optDouble("t1") + "，可以先賣一半"; }
                else if (p >= w.optDouble("entry_lo") && p <= w.optDouble("entry_hi")) { type = "buy"; msg = name + " 現在 " + p + "，進入建議買進區，可以考慮分批買進"; }
                String key = today + w.getString("code") + type;
                if (type != null && !seen.contains(key)) {
                    seen.add(key);
                    Notifier.show(c, "橘橘提醒：" + ("buy".equals(type) ? "可以買了" : "stop".equals(type) ? "該停損了" : "可以賣了"), msg);
                }
            }
        }
        Set<String> keep = new HashSet<>();
        for (String k : seen) if (k.startsWith(today)) keep.add(k);
        sp.edit().putStringSet("seen", keep).apply();
    }

    private static double num(String s) {
        try { return Double.parseDouble(s.replace(",", "")); } catch (Exception e) { return Double.NaN; }
    }
}

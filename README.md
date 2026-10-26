# 台股每日分析（橘橘老師）

免費、不需要 Claude 的台股分析網站與 Android App。

- **網站**：`https://aurora-bao77.github.io/tw-stock/`
  - iPhone：用 Safari 打開 → 分享 → 加入主畫面
  - Android：用 Chrome 打開 → ⋮ → 加到主畫面（或安裝下方 App）
- **股票小學堂**：`https://aurora-bao77.github.io/tw-stock/school/`
- **英文重新出發**：`https://aurora-bao77.github.io/tw-stock/english/`（給想重新學英文的大人：整句學、跟讀、間隔複習）
  - 「聊天」分頁的 AI 英文夥伴 Emma 用 Claude 回答，需在 Claude App 或 claude.ai 打開才能聊；GitHub 網站版其他功能都能用。
- **Android App**：安裝 `TwStock.apk`，可看盤中即時五檔，並在背景收到買賣點通知。

## 自動更新
GitHub Actions（`.github/workflows/update.yml`）會在週一到週五：
- 台灣時間 16:25 收盤後完整更新
- 09:05～13:35 每 30 分鐘更新盤中報價

也可以到 GitHub 的 **Actions → 每日更新台股分析網站 → Run workflow** 手動更新。

## 第一次設定
到 repository 的 **Settings → Pages → Build and deployment → Source** 選 **GitHub Actions**。

## 電腦版
`python tw_stock.py` 會開啟本機儀表板（每 15 秒即時報價）。

本工具依公開資料自動計算，僅供參考，不構成投資建議。

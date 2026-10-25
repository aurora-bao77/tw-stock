package tw.stock.app;

import android.Manifest;
import android.app.Activity;
import android.content.Context;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.webkit.JavascriptInterface;
import android.webkit.ValueCallback;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;

/** 台股分析 App：顯示免費網站，並提供網頁做不到的即時報價與手機通知 */
public class MainActivity extends Activity {
    private static final int PICK_FILE = 7;
    private WebView web;
    private ValueCallback<Uri[]> fileCallback;

    @Override
    protected void onCreate(Bundle state) {
        super.onCreate(state);
        web = new WebView(this);
        setContentView(web);
        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setCacheMode(isOnline() ? WebSettings.LOAD_DEFAULT : WebSettings.LOAD_CACHE_ELSE_NETWORK);
        web.addJavascriptInterface(new Bridge(this), "TWNative");
        final String site = getString(R.string.site_url);
        web.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest req) {
                Uri u = req.getUrl();
                if (u.toString().startsWith(site)) return false;
                startActivity(new Intent(Intent.ACTION_VIEW, u));   // 新聞等外部連結用瀏覽器開
                return true;
            }
        });
        web.setWebChromeClient(new WebChromeClient() {
            @Override
            public boolean onShowFileChooser(WebView v, ValueCallback<Uri[]> cb, FileChooserParams p) {
                fileCallback = cb;   // 「換圖片」選照片
                Intent i = new Intent(Intent.ACTION_GET_CONTENT).setType("image/*").addCategory(Intent.CATEGORY_OPENABLE);
                startActivityForResult(Intent.createChooser(i, "選擇圖片"), PICK_FILE);
                return true;
            }
        });
        if (Build.VERSION.SDK_INT >= 33 && checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED)
            requestPermissions(new String[]{Manifest.permission.POST_NOTIFICATIONS}, 1);
        Notifier.createChannel(this);
        AlertJobService.schedule(this);
        web.loadUrl(site);
    }

    @Override
    protected void onActivityResult(int req, int res, Intent data) {
        if (req == PICK_FILE && fileCallback != null) {
            Uri u = (res == RESULT_OK && data != null) ? data.getData() : null;
            fileCallback.onReceiveValue(u == null ? null : new Uri[]{u});
            fileCallback = null;
        }
        super.onActivityResult(req, res, data);
    }

    @Override
    public void onBackPressed() {
        if (web.canGoBack()) web.goBack(); else super.onBackPressed();
    }

    private boolean isOnline() {
        ConnectivityManager cm = (ConnectivityManager) getSystemService(Context.CONNECTIVITY_SERVICE);
        NetworkInfo n = cm == null ? null : cm.getActiveNetworkInfo();
        return n != null && n.isConnected();
    }

    /** 網頁裡的 window.TWNative */
    static class Bridge {
        private final Context ctx;
        Bridge(Context c) { ctx = c.getApplicationContext(); }

        @JavascriptInterface
        public String get(String url) { return Net.get(url); }

        @JavascriptInterface
        public void notify(String title, String body) { Notifier.show(ctx, title, body); }

        @JavascriptInterface
        public void saveWatch(String json) {
            ctx.getSharedPreferences("tw", Context.MODE_PRIVATE).edit().putString("watch", json).apply();
            AlertJobService.schedule(ctx);
        }
    }
}

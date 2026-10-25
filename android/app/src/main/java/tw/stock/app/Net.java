package tw.stock.app;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.URL;

/** 只允許連到證交所 / 櫃買中心 */
final class Net {
    private static final String[] HOSTS = {"mis.twse.com.tw", "www.twse.com.tw", "openapi.twse.com.tw", "www.tpex.org.tw"};

    static String get(String url) {
        try {
            URL u = new URL(url);
            boolean ok = "https".equals(u.getProtocol());
            boolean hostOk = false;
            for (String h : HOSTS) if (h.equals(u.getHost())) hostOk = true;
            if (!ok || !hostOk) return "{}";
            HttpURLConnection c = (HttpURLConnection) u.openConnection();
            c.setConnectTimeout(10000);
            c.setReadTimeout(10000);
            c.setRequestProperty("User-Agent", "Mozilla/5.0 (Linux; Android) TwStock/1.0");
            try (InputStream in = c.getInputStream()) {
                ByteArrayOutputStream out = new ByteArrayOutputStream();
                byte[] buf = new byte[8192];
                int n;
                while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
                return out.toString("UTF-8");
            } finally {
                c.disconnect();
            }
        } catch (Exception e) {
            return "{}";
        }
    }
}

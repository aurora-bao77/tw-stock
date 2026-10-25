package tw.stock.app;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.Context;
import android.content.Intent;
import android.os.Build;

final class Notifier {
    private static final String CH = "alerts";

    static void createChannel(Context c) {
        if (Build.VERSION.SDK_INT >= 26) {
            NotificationChannel ch = new NotificationChannel(CH, "買賣點提醒", NotificationManager.IMPORTANCE_HIGH);
            ch.setDescription("自選股到達買點、目標價或停損價時通知");
            c.getSystemService(NotificationManager.class).createNotificationChannel(ch);
        }
    }

    static void show(Context c, String title, String body) {
        createChannel(c);
        Intent open = new Intent(c, MainActivity.class).addFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        PendingIntent pi = PendingIntent.getActivity(c, 0, open, PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);
        Notification.Builder b = Build.VERSION.SDK_INT >= 26 ? new Notification.Builder(c, CH) : new Notification.Builder(c);
        b.setSmallIcon(android.R.drawable.ic_dialog_info).setContentTitle(title).setContentText(body)
                .setStyle(new Notification.BigTextStyle().bigText(body)).setAutoCancel(true).setContentIntent(pi);
        NotificationManager nm = (NotificationManager) c.getSystemService(Context.NOTIFICATION_SERVICE);
        nm.notify((int) (System.currentTimeMillis() % 100000), b.build());
    }
}

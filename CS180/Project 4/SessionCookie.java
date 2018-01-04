import java.util.Random;

/**
 * Created by Ryan on 11/4/2015.
 */
public class SessionCookie {
    public long ID;
    public long TimeOfActivity;
    public static int timeoutLength = 300;
    public SessionCookie(long id) {
        ID = id;
        TimeOfActivity = System.currentTimeMillis();
    }
    /*public SessionCookie() {
        Random r = new Random();
        ID = r.nextInt(9999);
        TimeOfActivity = System.currentTimeMillis();
    }*/
    public boolean hasTimedOut() {
        long currentTime = System.currentTimeMillis();
        long difference = currentTime - TimeOfActivity;
        if (difference > (timeoutLength*1000)) {
            return true;
        }
        return false;
    }
    public void updateTimeOfActivity() {
        long currentTime = System.currentTimeMillis();
        TimeOfActivity = currentTime;
    }
    public long getID() {
        return ID;
    }
    public static int generateID() {
        Random r = new Random();
        return r.nextInt(9999);
    }
}

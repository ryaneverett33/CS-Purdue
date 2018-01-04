import java.util.Random;

public class User {
    String username;
    String password;
    SessionCookie cookie;
    public User(String username, String password, SessionCookie cookie) {
        this.username = username;
        this.password = password;
        //It is valid for the user to not have a session cookie (i.e. the cookie has a null value,
        //this means the user is not connected).
        this.cookie = cookie;
    }
    public String getName() {
        return this.username;
    }
    public boolean checkPassword(String password) {
        //Such security
        if (this.password.equals(password)) {
            return true;
        }
        return false;
    }
    public SessionCookie getCookie() {
        return this.cookie;
    }
    public void setCookie(SessionCookie cookie) {
        this.cookie = cookie;
    }
}

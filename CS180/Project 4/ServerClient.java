/**
 * Created by Ryan on 11/7/2015.
 */
public class ServerClient {
    public static void main(String args[]) {
        User[] users = { new User("ryan","changer098",new SessionCookie(33)) };
        ChatServer cs = new ChatServer(users, 5);
        cs.run();
    }
}

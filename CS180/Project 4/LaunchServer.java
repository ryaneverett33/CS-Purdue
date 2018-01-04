
public class LaunchServer {

	/**
	 * This main method is for testing purposes only.
	 * @param args - the command line arguments
	 */
	public static void main(String[] args) {
		// Create a ChatServer and start it
		(new ChatServer(new User[0], 200)).run();
	}

}

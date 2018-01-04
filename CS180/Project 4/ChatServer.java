import java.util.*;

/**
 * <b> CS 180 - Project 4 - Chat Server Skeleton </b>
 * <p>
 * 
 * This is the skeleton code for the ChatServer Class. This is a private chat
 * server for you and your friends to communicate.
 * 
 * @author (Your Name) <(YourEmail@purdue.edu)>
 * 
 * @lab (Your Lab Section)
 * 
 * @version (Today's Date)
 *
 */
public class ChatServer {
	int userCount;
	User[] users;
    int maxMessages;
	CircularBuffer messages;
	public ChatServer(User[] users, int maxMessages) {
		this.maxMessages = maxMessages;
        this.userCount = 0;
        User[] tmp = new User[users.length+1];
        tmp[0] = new User("root", "cs180", null);
        this.userCount++;
        for (int i = 1; i < tmp.length; i++) {
            try {
                tmp[i] = users[i-1];
                //Will not reach this line if adding a user fails
                this.userCount++;
            }
            catch (Exception e) {
                System.out.println("User does not exist at i="+i);
                break;
            }
        }
        this.users = tmp;
		messages = new CircularBuffer(maxMessages);
	}

	/**
	 * This method begins server execution.
	 */
	public void run() {
		boolean verbose = false;
		System.out.printf("The VERBOSE option is off.\n\n");
		Scanner in = new Scanner(System.in);

		while (true) {
			System.out.printf("Input Server Request: ");
			String command = in.nextLine();

			// this allows students to manually place "\r\n" at end of command
			// in prompt
			command = replaceEscapeChars(command);

			if (command.startsWith("kill"))
				break;

			if (command.startsWith("verbose")) {
				verbose = !verbose;
				System.out.printf("VERBOSE has been turned %s.\n\n", verbose ? "on" : "off");
				continue;
			}

			String response = null;
			try {
				response = parseRequest(command);
			} catch (Exception ex) {
				response = MessageFactory.makeErrorMessage(MessageFactory.UNKNOWN_ERROR,
						String.format("An exception of %s occurred.", ex.getMessage()));
			}

			// change the formatting of the server response so it prints well on
			// the terminal (for testing purposes only)
			if (response.startsWith("SUCCESS\t"))
				response = response.replace("\t", "\n");

			// print the server response
			if (verbose)
				System.out.printf("response:\n");
			System.out.printf("\"%s\"\n\n", response);
		}

		in.close();
	}

	/**
	 * Replaces "poorly formatted" escape characters with their proper values.
	 * For some terminals, when escaped characters are entered, the terminal
	 * includes the "\" as a character instead of entering the escape character.
	 * This function replaces the incorrectly inputed characters with their
	 * proper escaped characters.
	 * 
	 * @param str
	 *            - the string to be edited
	 * @return the properly escaped string
	 */
	private static String replaceEscapeChars(String str) {
		str = str.replace("\\r", "\r");
		str = str.replace("\\n", "\n");
		str = str.replace("\\t", "\t");

		return str;
	}

	/**
	 * Determines which client command the request is using and calls the
	 * function associated with that command.
	 * 
	 * @param request
	 *            - the full line of the client request (CRLF included)
	 * @return the server response
	 */
	public String parseRequest(String request) {
		//"\r\n" indicates an end of line
		if (!request.endsWith("\r\n")) {
			return MessageFactory.makeErrorMessage(MessageFactory.UNKNOWN_COMMAND_ERROR);
		}
		//"Throw away \r\n , this works for some reason
		request = request.substring(0,(request.length()-2));
		String[] args = request.split("\t");
        if (args[0].equals("ADD-USER")) {
			if (args.length != 4) {
				return MessageFactory.makeErrorMessage(MessageFactory.FORMAT_COMMAND_ERROR);
			}
			return addUser(args);
        }
        else if (args[0].equals("USER-LOGIN")) {
			if (args.length != 3) {
				return MessageFactory.makeErrorMessage(MessageFactory.FORMAT_COMMAND_ERROR);
			}
			return userLogin(args);
        }
        else if (args[0].equals("POST-MESSAGE")) {
			if (args.length != 3) {
				return MessageFactory.makeErrorMessage(MessageFactory.FORMAT_COMMAND_ERROR);
			}
			//Find cookieID
			User user = null;
			int id;
			try {
				id = Integer.parseInt(args[1]);
			}
			catch (Exception e) {
				return MessageFactory.makeErrorMessage(MessageFactory.FORMAT_COMMAND_ERROR);
			}
			for (User u : users) {
				if (u.cookie == null) {
					continue;
				}
				if (u.cookie.getID() == id) {
					user = u;
					break;
				}
			}
			if (user == null) {
				//Couldn't find user
				return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
			}
			return postMessage(args, user.getName());
        }
        else if (args[0].equals("GET-MESSAGES")) {
			if (args.length != 3) {
				return MessageFactory.makeErrorMessage(MessageFactory.FORMAT_COMMAND_ERROR);
			}
			int cookie;
			try {
				cookie = Integer.parseInt(args[1]);
			}
			catch (Exception e) {
				return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
			}
			boolean found = false;
			for (User u : users) {
				if (u.getCookie() == null) {
					continue;
				}
				if (u.getCookie().getID() == cookie) {
					found = true;
					break;
				}
			}
			if (!found) {
				return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
			}
			return getMessages(args);
        }
		return MessageFactory.makeErrorMessage(MessageFactory.UNKNOWN_COMMAND_ERROR);
	}
	private boolean isValidString(String in, boolean username) {
		if (username) {
			//Usernames must be between 1 and 20 characters in length (inclusive)
			if (in.length() == 0) {
				return false;
			}
			else {
				if (in.length() > 20) {
					return false;
				}
			}
		}
		else {
			//Password must be between 4 and 40 characters in length (inclusive)
			if (in.length() < 4) {
				return false;
			}
			else {
				if (in.length() > 40) {
					return false;
				}
			}
		}
		char[] data = in.toCharArray();
		for (char c : data) {
			int letter = (int)c;
			if (letter > 64 && letter < 91) {
				continue;
			}
			else if (letter > 96 && letter < 123) {
				continue;
			}
			else if (letter > 47 && letter < 58) {
				continue;
			}
			else {
				return false;
			}
		}
		return true;
	}
    public String addUser(String[] args) {
		//returns SUCCESS or FAILED
		//a = 97, z = 122, A = 65, 90
		int cookieID;
		String username;
		String password;
		try {
			cookieID = Integer.parseInt(args[1]);
			username = args[2];
			password = args[3];
		}
		catch (Exception e) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		boolean exists = false;
		for (User u : users) {
			if (u.cookie == null) {
				continue;
			}
			if (u.cookie.getID() == cookieID) {
				exists = true;
				System.out.println("Found it!");
				break;
			}
		}
		if (!exists) {
			//Cookie doesn't exist, return the bullshit
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		if (!(isValidString(username, true)) || !(isValidString(password, false))) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		//check if the user already exists
		boolean aThing = false;
		for (User u : users) {
			if (u.username.equals(username)) {
				aThing = true;
				break;
			}
		}
		if (aThing) {
			return MessageFactory.makeErrorMessage(MessageFactory.USER_ERROR);
		}
        User newUser = new User(username,password,null);
		User tmp[] = new User[userCount+1];
		for (int i = 0; i < users.length; i++) {
			tmp[i] = users[i];
		}
		tmp[userCount] = newUser;
		users = tmp;
		userCount++;
		return SuccessMessages.makeGeneric();
    }
    public String userLogin(String[] args) {
		String username = args[1];
		String password = args[2];
		//Check for user
		User user = null;	//create a pointer for the user
		boolean found = false;
		for (User u : users) {
			if (u.getName().equals(username)) {
				user = u;
				found = true;
				System.out.println("Found it");
				break;
			}
		}
		if (!found) {
			return MessageFactory.makeErrorMessage(MessageFactory.USERNAME_LOOKUP_ERROR);
		}
		if (!(user.cookie == null)) {
			return MessageFactory.makeErrorMessage(MessageFactory.USER_CONNECTED_ERROR);
		}
		if (!(user.checkPassword(password))) {
			return MessageFactory.makeErrorMessage(MessageFactory.AUTHENTICATION_ERROR);
		}
		//If we've made it here, holy crap
		user.setCookie(new SessionCookie(SessionCookie.generateID()));
		return SuccessMessages.makeLogin((int)user.getCookie().getID());
    }
    public String postMessage(String[] args, String name) {
		char[] messageArray = args[2].toCharArray();
		boolean found = false;
		int cookie;
		for (char c : messageArray) {
			int character = (int)c;
			if (character != 32) {
				found = true;
				break;
			}
		}
		if (!found) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		try {
			cookie = Integer.parseInt(args[1]);
		}
		catch (Exception e) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		User user = null;	//pointer for the user we'll find
		for (User u : users) {
			if (u.getCookie() == null) {
				continue;
			}
			if (u.cookie.getID() == cookie) {
				user = u;
				break;
			}
		}
		if (user == null) {	//We couldn't find the user, respond accordingly
			return MessageFactory.makeErrorMessage(MessageFactory.USERNAME_LOOKUP_ERROR);
		}
		if (user.cookie.hasTimedOut()) {	//If cookie has timedout, respond
			return MessageFactory.makeErrorMessage(MessageFactory.COOKIE_TIMEOUT_ERROR);
		}
		String message = name + ": " + args[2];
		messages.put(message);
		return SuccessMessages.makeGeneric();
    }
    public String getMessages(String[] args) {
		int numMessages;
		try {
			numMessages = Integer.parseInt(args[2]);
		}
		catch (Exception e) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		if (numMessages <= 0) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		//Find user and check cookie
		int cookie;
		try {
			cookie = Integer.parseInt(args[1]);
		}
		catch (Exception e) {
			return MessageFactory.makeErrorMessage(MessageFactory.INVALID_VALUE_ERROR);
		}
		for (User u : users) {
			if (u.cookie == null) continue;
			if (u.cookie.getID() == cookie) {
				if (u.cookie.hasTimedOut()) {
					return MessageFactory.makeErrorMessage(MessageFactory.COOKIE_TIMEOUT_ERROR);
				}
			}
		}
		String result = SuccessMessages.makeMessages(messages.getNewest(numMessages));
		if (result.equals("BADFAIL")) {
			return MessageFactory.makeErrorMessage(MessageFactory.UNKNOWN_ERROR);
		}
		return result;
    }
}

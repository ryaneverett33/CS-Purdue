import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import org.junit.rules.Timeout;

/**
 * <b> CS 180 - Project 4 - Chat Server Test Samples </b>
 * <p>
 *
 *
 * @author (Your Name) <(YourEmail@purdue.edu)>
 *
 * @lab (Your Lab Section)
 *
 * @version (Today's Date)
 *
 */
public class Project4Test {

	@Before
	public void setUp() {
		SessionCookie.timeoutLength = 300;
	}

	// Auxilary function
	private static String  verifyErrorMessage(String msg, int code) {

		if (!msg.endsWith("\r\n"))
			return "Invalid Error Message Format";

		String[] st = msg.split("\t");
		if (st.length != 3) {
			return "Invalid Error Message Format";
		}
		String ta = String.valueOf(code);

		if (!"FAILURE".equals(st[0]))
			return "Invalid Error Message Format";
		if (!ta.equals(st[1]))
			return String.format("expected error code %d, but received %s", code, st[1]);

		return "";
	}

	private static boolean verifyMessages(String res, int idx, String user, String msg) {

		int idxP = res.indexOf(')');
		if (idxP < 0)
			return false;

		int idxS = res.indexOf(':');
		if (idxS < 0)
			return false;

		String number = res.substring(0, idxP).trim();
		String name = res.substring(idxP + 1, idxS).trim();
		String m = res.substring(idxS + 1).trim();

		return number.length() == 4 && name.equals(user) && msg.equals(m) && String.format("%04d", idx).equals(number);
	}

	/********************************************************************************************************
	 *
	 * SessionCookie
	 *
	 ********************************************************************************************************/

	// TODO you should write some tests

	/********************************************************************************************************
	 *
	 * CircularBuffer
	 *
	 ********************************************************************************************************/

	// TODO you should write some tests

	/********************************************************************************************************
	 *
	 * User
	 *
	 ********************************************************************************************************/

	// TODO you should write some tests

	/********************************************************************************************************
	 *
	 * ChatServer.addUser
	 *
	 ********************************************************************************************************/

	@Test//(timeout=1000)
	public void testAddUserNominal() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.addUser(new String[] { "ADD-USER", "42", "cs240", "hereicome" });
		String ta = "SUCCESS\r\n";

		assertEquals(
				"ChatServer: 'addUser' doesn't return correct success message or didn't succeed when it should have.",
				ta, student);

		student = chatServer.userLogin(new String[] { "USER-LOGIN", "cs240", "hereicome" });
		assertTrue("ChatServer: 'addUser' test fails because 'userLoggin' can not log with the newly added user",
				student.startsWith("SUCCESS"));
	}

	@Test(timeout=1000)
	public void testAddUserInvalidUsername() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.addUser(new String[] { "ADD-USER", "42", "", "hereicome" });
		String msg = verifyErrorMessage(student, MessageFactory.INVALID_VALUE_ERROR);
		assertTrue("addUser:" + msg, "".equals(msg));

		student = chatServer.addUser(new String[] { "ADD-USER", "42", "aaa-bbb", "hereicome" });
		msg = verifyErrorMessage(student, MessageFactory.INVALID_VALUE_ERROR);
		assertTrue("addUser:" + msg, "".equals(msg));
	}

	@Test(timeout=1000)
	public void testAddUserInvalidPassword() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.addUser(new String[] { "ADD-USER", "42", "cs240", "hereicome!" });
		String msg = verifyErrorMessage(student, MessageFactory.INVALID_VALUE_ERROR);
		assertTrue("addUser:" + msg, "".equals(msg));

		student = chatServer.addUser(new String[] { "ADD-USER", "42", "ee", "herei(c)ome" });
		msg = verifyErrorMessage(student, MessageFactory.INVALID_VALUE_ERROR);
		assertTrue("addUser:" + msg, "".equals(msg));
	}

	/********************************************************************************************************
	 *
	 * ChatServer.userLogin
	 *
	 ********************************************************************************************************/
	@Test(timeout=1000)
	public void testRootUser() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.userLogin(new String[] { "USER-LOGIN", "root", "cs180" });
		assertTrue("ChatServer: can not log as root user", student.matches("SUCCESS\t\\d+\r\n"));
	}

	@Test(timeout=1000)
	public void testUserLoginNominal() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", null);
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.userLogin(new String[] { "USER-LOGIN", "greg", "greg" });
		assertTrue("ChatServer: 'userLogin' incorrect response format", student.endsWith("\r\n"));
		assertTrue("ChatServer: 'userLogin' can not log in with a valid user", student.matches("SUCCESS\t\\d+\r\n"));
	}

	/********************************************************************************************************
	 *
	 * ChatServer.postMessage
	 *
	 ********************************************************************************************************/

	@Test(timeout=1000)
	public void testPostMessageNominal() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String ta = "SUCCESS\r\n";
		String student = chatServer.postMessage(new String[] { "POST-MESSAGE", "42", "Hello, world!!" },  "varun");

		assertEquals("ChatServer: 'postMessage' failed when it shouldn't have.",
				ta, student);
	}

	@Test//(timeout=1000)
	public void testPostMessageEmptyMessage() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.postMessage(new String[] { "POST-MESSAGE", "42", " " }, "greg");
		String msg = verifyErrorMessage(student, MessageFactory.INVALID_VALUE_ERROR);
		assertTrue("postMessage:" + msg, "".equals(msg));
	}

	/********************************************************************************************************
	 *
	 * ChatServer.getMessages
	 *
	 ********************************************************************************************************/

	//@Test(timeout=1000)
	@Test()
	public void testGetMessagesNominal() {
		User[] users = new User[1];
		User greg = new User("greg","greg", new SessionCookie(42));
		SessionCookie.timeoutLength = 1000;
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String msg = "Hello, world!!";

		String ta = "SUCCESS\r\n";
		String student = chatServer.postMessage(new String[] { "POST-MESSAGE", "42", msg },  "greg");

		assertEquals("ChatServer: 'getMessage' test failed because 'postMessage' did not work", ta, student);

		student = chatServer.getMessages(new String[] { "GET-MESSAGES", "42", "1" });
		String[] test = chatServer.messages.getNewest(1);
		test = test;

		assertTrue("ChatServer: 'getMessage' incorrect response format", student.endsWith("\r\n"));

		String[] tab = student.trim().split("\t");
		assertEquals("ChatServer: 'getMessage' invalid return value (1 msg sent, 1 requested)", 2,
				tab.length);
		assertTrue("ChatServer: 'getMessage' invalid return value (1 msg sent, 1 requested)",
				verifyMessages(tab[1], 0, "greg", msg));
	}

	/********************************************************************************************************
	 *
	 * ChatServer.parseRequest
	 *
	 ********************************************************************************************************/
	@Test//(timeout=1000)
	public void testAddUserWrongFormat() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.parseRequest("ADD-USER\t42\tcs240\thereicome\tmoreparam\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue(msg,"".equals(msg));
		//assertTrue("parseRequest:" + msg, "".equals(msg));

		student = chatServer.parseRequest("ADD-USER\r\n");
		msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));
	}

	@Test(timeout=1000)
	public void testUserLoginWrongFormat() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.parseRequest("USER-LOGIN\troot\tcs180\tmoreparam\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));

		student = chatServer.parseRequest("USER-LOGIN\trootu\r\n");
		msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));
	}

	@Test(timeout=1000)
	public void testGetMessageWrongFormat() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.parseRequest("GET-MESSAGES\t42\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));

		student = chatServer.parseRequest("GET-MESSAGES\r\n");
		msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));
	}

	@Test(timeout=1000)
	public void testPostMessageWrongFormat() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.parseRequest("POST-MESSAGE\t42\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));

		student = chatServer.parseRequest("POST-MESSAGE\r\n");
		msg = verifyErrorMessage(student, MessageFactory.FORMAT_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));
	}

	@Test(timeout=1000)
	public void testInvalidCommand() {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		String student = chatServer.parseRequest("GET-MESSAGE\t42\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.UNKNOWN_COMMAND_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));
	}

	@Test(timeout=1000)
	public void testCookieValidity() throws InterruptedException {
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);

		SessionCookie.timeoutLength = 0;
		Thread.sleep(10);
		String student = chatServer.parseRequest("GET-MESSAGES\t42\t1\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.COOKIE_TIMEOUT_ERROR);
		assertTrue("parseRequest:" + msg, "".equals(msg));

		student = chatServer.parseRequest("GET-MESSAGES\t42\t1\r\n");
		msg = verifyErrorMessage(student, MessageFactory.LOGIN_ERROR);
		assertTrue("parseRequest:" + msg + " (after timeout)", "".equals(msg));
	}

	@Test(timeout=10000)
	public void testUpdateCookieGetMessage() throws InterruptedException {

		/* Get messages */
		User[] users = new User[1];
		users[0] = new User("greg", "greg", new SessionCookie(42));
		ChatServer chatServer = new ChatServer(users, 100);
		chatServer.messages.put("test: testmessage");
		chatServer.parseRequest("USER-LOGIN\tgreg\tgreg\r\n");
		SessionCookie.timeoutLength = 1;
		//Thread.sleep(800);
		Thread.sleep(1200);
		String student = chatServer.parseRequest("GET-MESSAGES\t42\t1\r\n");
		assertTrue("ChatServer: 'parseRequest' test failed because 'GET-MESSAGES' failed.",
				student.startsWith("SUCCESS"));
		Thread.sleep(400);
		//student = chatServer.parseRequest("GET-MESSAGES\t42\t0\r\n");	//Broken
		student = chatServer.parseRequest("GET-MESSAGES\t42\t1\r\n");
		String msg = verifyErrorMessage(student, MessageFactory.COOKIE_TIMEOUT_ERROR);
		assertTrue("Check your Cookie Management:" + msg, "".equals(msg));
	}

	@Test
	public void testGetLatest() throws Exception {
		//Make sure our getLatest works
		CircularBuffer cb = new CircularBuffer(5);
		cb.put("Surprise");
		cb.put("Hellop");
		int latest = 1;
		assertEquals(latest, cb.getLatest());
		cb.put("jack");
		cb.put("reddit");
		cb.put("penis");
		int instance = 4;
		assertEquals(instance, cb.getLatest());
		cb.put("helloagain");
		int open = 0;
		assertEquals(open, cb.getLatest());
	}
	@Test
	public void testGetNewestNotRolledOver() throws Exception {
		CircularBuffer cb = new CircularBuffer(2);
		cb.put("Surprise");
		cb.put("Hellop");
		String[] actual = { "0001) Hellop", "0000) Surprise" };
		assertEquals(cb.getNewest(2),actual);
		String[] other  = { "0001) Hellop" };
		assertEquals(cb.getNewest(1),other);
		CircularBuffer cb2 = new CircularBuffer(10);
		cb2.put("Surprise");
		cb2.put("Hellop");
		cb2.put("goneaway");
		cb2.put("goner");
		String[] again = { "0003) goner", "0002) goneaway" };
		assertEquals(cb2.getNewest(2),again);
	}
	@Test
	public void testGetNewestRolledOver() throws Exception {
		//Test only one loop
		CircularBuffer cb = new CircularBuffer(3);
		cb.put("gottata");
		cb.put("hjack");
		cb.put("substantial");
		cb.put("red");
		cb.put("tube");
		String[] s = { "0004) tube", "0003) red" };
		assertEquals(cb.getNewest(2),s);
		//Test both loops
		String[] s2 = { "0004) tube", "0003) red", "0002) substantial" };
		String[] newest = cb.getNewest(3);
		assertEquals(cb.getNewest(3),s2);
	}
	@Test
	public void testRollingOver() throws Exception {
		CircularBuffer cb = new CircularBuffer(3);
		cb.put("gottata");
		cb.put("hjack");
		cb.put("substantial");
		cb.put("red");
		String s[] = { "0003) red","0002) substantial" };
		assertEquals(s, cb.getNewest(2));
		cb.put("jarvis");
		cb.put("tony");
		cb.put("johnny");
		String s2[] = { "0006) johnny","0005) tony","0004) jarvis" };
		assertEquals(s2, cb.getNewest(3));
	}
	@Test
	public void testNumberOverflow() throws Exception {
		CircularBuffer cb = new CircularBuffer(10);
		for (int i = 0; i < 10020; i++) {
			cb.put("test");
		}
		String[] s = { "0019) test" };
		assertEquals(s,cb.getNewest(1));
		cb.put("jack");
		cb.put("purd");
		String[] s2 = { "0021) purd","0020) jack","0019) test","0018) test" };
		assertEquals(cb.getNewest(4),s2);
	}
}

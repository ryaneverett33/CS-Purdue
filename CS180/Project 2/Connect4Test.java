import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by Ryan on 9/30/2015.
 */
public class Connect4Test {
    Connect4 c = new Connect4();

    @Test(timeout = 100)
    public void testPutPieceYellow() throws Exception {
        String message = "Test Putting a Yellow Piece: X";
        assertEquals(message, c.putPiece(0, Connect4.YELLOW), 5);
    }

    public void testPutPieceRed() throws Exception {
        String message = "Test Putting a Yellow Piece: X";
        assertEquals(message, c.putPiece(0, Connect4.RED), 4);
    }

    /*@Test
    public void testCheckAlignment() throws Exception {

    }*/
}

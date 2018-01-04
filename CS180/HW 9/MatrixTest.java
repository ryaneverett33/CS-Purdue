import org.junit.Test;
import org.junit.*;

import static org.junit.Assert.*;

/**
 * Created by Ryan on 10/2/2015.
 */
public class MatrixTest {

    Matrix m;
    @Before
    public void Setup() throws Exception {
        m = new Matrix();
    }
    @Test
    public void testReshapePass() throws Exception {
        int[] vector = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
        int[][] actual = {{1, 2, 3, 4, 5, 6}, {7, 8, 9, 10, 11, 12}};
        String message = "test Reshape that should Pass";
        assertEquals(message, actual, m.reshape(vector, 2, 6));
    }
    @Test
    public void testReshapePass2() throws Exception {
        int[] vector = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
        int[][] actual = {{1, 2, 3, 4}, {5, 6, 7, 8}, {9, 10, 11, 12}}; //[[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]
        String message = "test Reshape that should Pass 2";
        assertEquals(message, actual, m.reshape(vector, 3, 4));
    }
}
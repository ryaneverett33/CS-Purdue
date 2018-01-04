import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by Ryan on 11/2/2015.
 */
public class MatrixTest {

    @Test
    public void testWriteMatrix() throws Exception {
        Matrix m = new Matrix();
        m.writeMatrix("matrix.txt", new int[][]{{1, 2, 3}, {4, 5, 6}, {7, 8, 9}});
    }
}
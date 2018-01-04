import org.junit.*;
import static org.junit.Assert.*;

import static org.junit.Assert.*;

/**
 * Created by Ryan on 9/30/2015.
 */
public class MatrixTest {
    Matrix m;
    @Before
    public void setUp() throws Exception {
        m = new Matrix();
    }
    @Test(timeout = 100)
    public void testIsSymmetricPass() throws Exception {
        int[][] matrix = {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}};
        String message = "Test if isSymmetric when it is diagonal";
        boolean actual = true;
        assertEquals(message,m.isSymmetric(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsSymmetricPass2() throws Exception {
        int[][] matrix = {{0,1,2},{1,0,3},{2,3,0}};
        String message = "Test if isSymmetric when it is diagonal 2 ";
        boolean actual = true;
        assertEquals(message,m.isSymmetric(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsSymmetricFail() throws Exception {
        int[][] matrix = {{0,5,2},{1,0,3},{2,3,0}};
        String message = "Test if isSymmetric when it isn't diagonal";
        boolean actual = false;
        assertEquals(message,m.isSymmetric(matrix),actual);
    }
    @Test(timeout = 100)
     public void testIsDiagonalPass() throws Exception {
        int[][] matrix = {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}};
        String message = "Test if IsDiagonal when it is diagonal";
        boolean actual = true;
        assertEquals(message,m.isDiagonal(matrix),actual);
    }
    @Test(timeout = 100)
     public void testIsDiagonalFail() throws Exception {
        int[][] matrix = {{1,0,1,0},{0,1,0,0},{1,0,1,0},{0,0,0,1}};
        String message = "Test if IsDiagonal when it isn't diagonal";
        assertEquals(message,m.isDiagonal(matrix),false);
    }
    @Test(timeout = 100)
    public void testIsDiagonalFail2() throws Exception {
        int[][] matrix = {{1, 1, 1, 1}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}};
        String message = "Test if IsDiagonal when it isn't diagonal...again";
        assertEquals(message, m.isDiagonal(matrix), false);
    }
    @Test(timeout = 100)
    public void testIsIdentityPass() throws Exception {
        int[][] matrix = {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}};
        String message = "Test if IsIdentity when it is an identity";
        boolean actual = true;
        assertEquals(message,m.isIdentity(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsIdentityFail() throws Exception {
        int[][] matrix = {{1,0,0,1},{0,1,0,0},{0,0,1,0},{0,0,0,1}};
        String message = "Test if IsIdentity when it is an identity";
        boolean actual = false;
        assertEquals(message,m.isIdentity(matrix),actual);
    }
    @Test(timeout = 100)
     public void testIsIdentityFail2() throws Exception {
        int[][] matrix = {{1,0,0,0},{0,5,0,0},{0,0,1,0},{0,0,0,1}};
        String message = "Test if IsIdentity when it is an identity 2";
        boolean actual = false;
        assertEquals(message,m.isIdentity(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsUpperTriangularPass() throws Exception {
        int[][] matrix = {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}};
        String message = "Test if isUpperTriangle when it is a UpperTriangle";
        boolean actual = true;
        assertEquals(message,m.isUpperTriangular(matrix),actual);
    }
    @Test(timeout = 100)
     public void testIsUpperTriangularPass2() throws Exception {
        int[][] matrix = {{2,0,0,2,0},{0,3,0,0,0},{0,0,3,0,3},{0,0,0,3,0},{0,0,0,0,2}};
        String message = "Test if isUpperTriangle when it is a UpperTriangle 2 ";
        boolean actual = true;
        assertEquals(message,m.isUpperTriangular(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsTriDiagonalPass() throws Exception {
        int[][] matrix = {{1,1,0,0},{1,1,1,0},{0,1,1,1},{0,0,1,1}};
        String message = "Test if isTriDiagonal when it is a TriDiagonal";
        boolean actual = true;
        assertEquals(message,m.isTridiagonal(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsTriDiagonalPass2() throws Exception {
        int[][] matrix = {{1,1,0,0,0,0},{1,1,1,0,0,0},{0,1,1,1,0,0},{0,0,1,1,1,0},{0,0,0,1,1,1},{0,0,0,0,1,1}};
        String message = "Test if isTriDiagonal when it is a TriDiagonal again";
        boolean actual = true;
        assertEquals(message,m.isTridiagonal(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsTriDiagonalFail() throws Exception {
        int[][] matrix = {{1,1,0,5,0,0},{1,1,1,0,0,0},{0,1,1,1,0,0},{0,0,1,1,1,0},{5,0,0,1,1,1},{0,0,0,0,1,1}};
        String message = "Test if isTriDiagonal when it isn't a TriDiagonal again";
        boolean actual = false;
        assertEquals(message,m.isTridiagonal(matrix),actual);
    }
    @Test(timeout = 100)
    public void testIsTriDiagonalFail2() throws Exception {
        int[][] matrix = {{1,1,0,0,0,0},{1,1,1,0,0,0},{0,1,1,1,0,0},{0,0,1,1,1,0},{0,0,0,1,1,1},{0,0,0,1,1,1}};
        String message = "Test if isTriDiagonal when it isn't a TriDiagonal again";
        boolean actual = false;
        assertEquals(message,m.isTridiagonal(matrix),actual);
    }
}
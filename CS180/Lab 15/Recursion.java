import java.io.*;

/**
 * Created by Ryan on 12/8/2015.
 */
public class Recursion {
    public static int determinant(int[][] matrix) {
        if (matrix.length == 1 && matrix[0].length == 1) {
            //If matrix is size 1x1
            return matrix[0][0];
        }
        else {
            int d = 0;
            //Loop through each element i in the first (0th) row of the matrix.
            for (int i = 0; i < matrix.length; i++) {
                int[][] A = new int[matrix.length - 1][matrix[0].length - 1];
                for (int j = 1; j < matrix.length; j++) {
                    for (int k = 1; k < matrix[0].length; k++) {
                        A[j-1][k-1] = matrix[j][k];
                    }
                }
                int det = determinant(A);
                if (det * i % 2 != 0) {
                    d = d - det;
                }
                else {
                    d = d + det;
                }
            }
            return d;
        }
    }
    public static int filecount (File f) {
        if (f.isFile()) {
            return 1;
        }
        else {
            int count = 0;
            File[] files = f.listFiles();
            for (File tmpFile : files) {
                count = count + filecount(tmpFile);
            }
            return count;
        }
    }
}

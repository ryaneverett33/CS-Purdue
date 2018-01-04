/**
 * Created by Ryan on 9/30/2015.
 */
public class Matrix {
    //proper matrix stuff. matrix[row][column]
    boolean isValidMove(int[][] matrix, int i, int j) {
        try {
            int x = matrix[i][j];
        }
        catch (Exception e) {
            return false;
        }
        return true;
    }
    public boolean isSymmetric(int[][] matrix) {
        // isSymmetric: determines if a matrix is symmetric with respect to its main diagonal.
        // To be symmetric, the matrix must be a square n×n matrix and the (i,j) entry must be equal to the (j,i) entry.
        for (int i = 0; i < matrix[0].length; i++) {
            //rows second
            for (int j = 0; j < matrix.length; j++) {
                if(matrix[j][i] != matrix[i][j] ) {
                    return false;
                }
            }
        }
        return true;
    }
    public boolean isDiagonal(int[][] matrix) {
        // isDiagonal: determines if a matrix is a diagonal matrix.
        // To be a diagonal matrix, all entries that do not lie on the main diagonal must equal 0.
        /*int[] row = new int[10];
        int[] column = new int[10];
        int mainDiagLength = 0;
        boolean looping = true;*/

        //columns first
        int skipI = 0;
        int skipJ = 0;

        for (int i = 0; i < matrix[0].length; i++) {
            //rows second
            for (int j = 0; j < matrix.length; j++) {
                if (i == skipI && j == skipJ) {
                    skipI++;
                    skipJ++;
                    continue;
                }
                if (matrix[j][i] != 0) {
                    return false;
                }
            }
        }
        return true;

    }
    public boolean isIdentity(int[][] matrix) {
        // isIdentity: determines if a matrix is an identity matrix.
        // To be an identity matrix, the matrix must be a square n×n matrix, all entries along the
        // main diagonal must equal 1, and all other entries must equal 0.
        if(!isDiagonal(matrix)) {
            return false;
        }
        int i = 0;
        int j = 0;
        boolean done = false;
        while(!done) {
            if(!isValidMove(matrix, i, j)) {
                done = true;
                break;
            }
            if(matrix[j][i] != 1) {
                return false;
            }
            i++;
            j++;
        }
        return true;
    }
    public boolean isUpperTriangular(int[][] matrix) {
        // isUpperTriangular: determines if a matrix is an upper triangular matrix.
        // To be an upper triangular matrix, the matrix must be a square n×n matrix and all entries
        // below the main diagonal must equal 0.
        boolean done = false;
        int i = -1;
        int j = 0;
        while(!done) {
            i++;
            if (i == 0+j && j == 0+j) {
                j++;
                i = -1;
                continue;
            }
            if (!isValidMove(matrix,i,j)) {
                done = true;
                break;
            }
            if (matrix[j][i] != 0) {
                return false;
            }
        }
        return true;
    }
    public boolean isTridiagonal(int[][] matrix) {
        // isTriDiagonal: determines if a matrix is a tridiagonal matrix.
        // To be a tridiagonal matrix, the matrix must be a square n×n matrix, all entries must
        // equal 0 except the main diagonal, the upper diagonal and the lower diagonal.
        int mainI = 0;
        int mainJ = 0;
        int upperI = 0;
        int upperJ = 1;
        int lowerI = 1;
        int lowerJ = 0;

        for (int i = 0; i < matrix[0].length; i++) {
            //rows second
            for (int j = 0; j < matrix.length; j++) {
                if (i == mainI && j == mainJ) {
                    mainI++;
                    mainJ++;
                    continue;
                }
                if (i == upperI && j == upperJ) {
                    upperI++;
                    upperJ++;
                    continue;
                }
                if (i == lowerI && j == lowerJ) {
                    lowerI++;
                    lowerJ++;
                    continue;
                }
                if (matrix[j][i] != 0) {
                    return false;
                }
            }
        }
        return true;
    }
}

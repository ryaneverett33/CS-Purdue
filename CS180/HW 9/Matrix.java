/**
 * Created by Ryan on 10/1/2015.
 */
public class Matrix {
    public boolean isReshapable(int length, int row, int col) {
        if (length < 0 || row < 0 || col < 0) {
            return false;
        }
        if (length == 0 && row == 0 && col == 0) {
            return true;
        }
        if (length == 0) {
            if (row > 0 || col > 0)
                return false;
        }
        if (row * col == length) {
            return true;
        }
        return false;
    }
    int[][] reshape(int[] vector, int row, int col) {
        if (!isReshapable(vector.length, row, col)) {
            return null;
        }
        if (vector == null) {
            return null;
        }
        int[][] matrix = new int[row][col];
        int count = 0;
        //rows first
        for (int i = 0; i < row; i++) {
            //columns next
            for (int j = 0; j < col; j++) {
                matrix[i][j] = vector[count];
                count++;
            }
        }
        return matrix;
    }
}

/**
 * Created by Ryan on 10/1/2015.
 */
import java.util.Arrays;
import java.io.*;
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
    int[] readVector(String filename) {
        //For the dumb cases
        if (filename == null || filename.length() == 0) {
            System.out.println("File empty");
            return null;
        }
        FileReader justData;
        try {
            justData = new FileReader(filename);
        }
        catch (FileNotFoundException e) {
            System.out.println("File not found");
            return null;
        }
        BufferedReader reader = new BufferedReader(justData);
        String[] s;
        try {
            s = reader.readLine().split(",");
        }
        catch (Exception e) {
            System.out.println("Could not split");
            return null;
        }
        for (String strings : s) {
            System.out.println(s);
        }
        int[] matrix = new int[s.length];
        for (int i = 0; i < matrix.length; i++) {
            matrix[i] = Integer.parseInt(s[i]);
        }
        return matrix;
    }
}

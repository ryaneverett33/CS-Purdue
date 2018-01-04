/**
 * Created by Ryan on 10/1/2015.
 */
import java.util.ArrayList;
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
    void writeMatrix(String filename, int[][] matrix) {
        File f = new File(filename);
        PrintWriter pw;
        if (f.exists()) {
            System.out.println("File already exists, overwriting");
            try {
                f.createNewFile();
            }
            catch (IOException e) {
                System.out.println("Failed to create file");
            }
        }
        try {
            pw = new PrintWriter(f);
        }
        catch (FileNotFoundException e) {
            System.out.println("Failed to find file");
            return;
        }
        ArrayList<String> rows = new ArrayList<>();
        String tmp = new String();
        int jLen = 0;
        int iLen = 0;
        try {
            iLen = matrix.length;
        }
        catch (Exception e) {
            System.out.println("This is dumb");
            return;
        }
        try {
            jLen = matrix[0].length;
        }
        catch (Exception e) {
            System.out.println("This is also dumb");
            return;
        }
        System.out.println("Outer loop: " + matrix.length);
        System.out.println("Inner loop: " + matrix[0].length);
        for (int i = 0; i < matrix.length; i++) {
            for (int j = 0; j < matrix[i].length; j++) {
                if (j == 0 && matrix[i].length > 1) {
                    tmp = new String();
                    int foo = matrix[i][j];
                    tmp = Integer.toString(foo) + ",";
                    System.out.println("tmp at j=0: " + tmp);
                }
                else if (j > 0 && j < (matrix[i].length - 1)) {
                    //Add to string
                    int foo = matrix[i][j];
                    tmp += Integer.toString(foo) + ",";
                    System.out.println("tmp at j>0: " + tmp);
                }
                else if (j == (matrix[i].length - 1)) {
                    int foo = matrix[i][j];
                    tmp += Integer.toString(foo);   //Don't append comma
                    rows.add(tmp);
                    System.out.println("Final: " + tmp);
                }
                else if (matrix[i].length == 1) {
                    rows.add("" + matrix[i][j]);
                    System.out.println("Length of one: " + matrix[i][j]);
                }
                else {
                    System.out.println("Shouldn't have reached this");
                    return;
                }
            }
        }
        System.out.println("Begin writing data");
        System.out.println("Rows: " + rows.size());
        for (int i = 0; i < rows.size(); i++) {
            System.out.println(rows.get(i));
            pw.println(rows.get(i));
        }
        pw.flush();
    }
}

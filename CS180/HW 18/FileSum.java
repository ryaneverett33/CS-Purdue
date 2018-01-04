/**
 * Created by Ryan on 11/12/2015.
 */

import java.io.*;
import java.util.*;

public class FileSum {
    public static double sumFile(String filename) {
        // Read each line to array
        // Read each word to array
        // Read each number to array
        // Sum number array
        if (filename == null || filename.length() == 0) {
            return 0;
        }
        File f = new File(filename);
        Scanner s;
        try {
            s = new Scanner(f);
        }
        catch (Exception e) {
            System.out.println("File not found.");
            return 0;
        }
        ArrayList<String> lines = new ArrayList<>();
        while (s.hasNext()) {
            lines.add(s.nextLine());
        }
        ArrayList<Double> numbers = new ArrayList<>();
        for (String line : lines) {
            String[] words = line.split(" ");
            for (String word : words) {
                //try and parse it
                try {
                    double number = Double.parseDouble(word);
                    numbers.add(number);
                }
                catch (Exception e) {
                    continue;
                }
            }
        }
        double sum = 0;
        for (Double d : numbers) {
            sum = sum + d;
        }
        return sum;
    }

    public static void main(String args[]) {
        double d = FileSum.sumFile("example.txt");
        System.out.println(d);
    }
}

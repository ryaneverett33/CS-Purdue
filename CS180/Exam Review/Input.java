/**
 * Created by Ryan on 11/10/2015.
 */
import java.io.*;
import java.util.*;
public class Input {
    public void writeln(String foo) {
        System.out.println(foo);
    }
    public static void main(String args[]) {
        File f = new File("read.txt");
        Output out = new Output();
        if (!f.canRead()) {
            out.writeln("Cannot read file");
            return;
        }
        Scanner s;
        try {
            s = new Scanner(f);
        }
        catch (Exception e) {
            out.writeln("File not found.");
            return;
        }
    }
}

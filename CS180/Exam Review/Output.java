/**
 * Created by Ryan on 11/10/2015.
 */
import java.io.*;
public class Output {
    public void writeln(String foo) {
        System.out.println(foo);
    }
    public static void main(String args[]) {
        File f = new File("write.txt");
        Output out = new Output();
        try {
            f.createNewFile();
        }
        catch (Exception e) {
            out.writeln("failed to create file");
        }
        
    }
}

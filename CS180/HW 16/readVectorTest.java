/**
 * Created by Ryan on 10/29/2015.
 */
import java.util.Arrays;
public class readVectorTest {
    public static void main(String[] args) {
        Matrix m = new Matrix();
        System.out.println(Arrays.toString(m.readVector("vector.txt")));
    }
}

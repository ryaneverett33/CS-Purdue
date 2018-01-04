import static org.junit.Assert.*;
import org.junit.Test;
/**
 * Created by Ryan on 12/5/2015.
 */
public class evaluateTest {

    @Test(timeout=1000)
    public void testEqual() throws Exception {
        assertEquals(3.0,evaluate.equal("1+2"),0.0000001);
        assertEquals(6.0,evaluate.equal("1+2+3"),0.0000001);
        assertEquals(34.0,evaluate.equal("1+2+5+7+9+10"),0.0000001);
    }
    @Test(timeout = 1000)
    public void testEqualSub() {
        assertEquals(1.0,evaluate.equal("3-2"),0.0000001);
        assertEquals(3.0,evaluate.equal("10-5-2"),0.0000001);
        assertEquals(2.0,evaluate.equal("22-2-4-6-8"),0.0000001);
    }
    @Test(timeout = 1000)
    public void testEqualAddSub() {
        assertEquals(25.0,evaluate.equal("15+12-2"),0.0000001);
        assertEquals(26.0,evaluate.equal("22-2-4+10"),0.0000001);
        assertEquals(17.0,evaluate.equal("17-17+17-17+17"),0.0000001);
    }
}
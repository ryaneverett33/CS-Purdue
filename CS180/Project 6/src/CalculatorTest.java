import static org.junit.Assert.*;

import org.junit.*;

/**
 * Created by Ryan on 12/6/2015.
 */
public class CalculatorTest {
    Calculator calc;
    tester test;
    @Before
    public void Setup() {
        test = new tester();
        calc = new Calculator(test);
    }
    @Test (timeout = 1000)
    public void testExample1() {
        calc.inputDigit('4');
        calc.operator('+');
        calc.inputDigit('5');
        assertEquals("4 + 5",test.getDisplay());
        calc.delete();
        assertEquals("4 +", test.getDisplay());
        calc.inputDigit('6');
        calc.equal();
        assertEquals("10.00",test.getDisplay());
    }
    @Test (timeout = 1000)
    public void testExample2() {
        calc.inputDigit('4');
        calc.equal();
        assertEquals(test.invalid, true);
        calc.inputDigit('5');
        calc.delete();
        assertEquals(test.getDisplay(),"4");
        calc.operator('/');
        calc.inputDigit('3');
        assertEquals(test.getDisplay(),"4 / 3");
        calc.equal();
        assertEquals(test.getDisplay(),"1.33");
        //Second half, I think this will break
        calc.inputDigit('9');
        assertEquals(test.getDisplay(),"9");
        calc.operator('+');
        assertEquals(test.getDisplay(),"9 +");
        calc.inputDigit('1');
        calc.equal();
        assertEquals(test.getDisplay(),"10.00");
    }
    @Test (timeout = 1000)
    public void testExample3() {
        calc.inputDigit('0');
        calc.operator('/');
        calc.inputDigit('0');
        assertEquals(test.getDisplay(),"0 / 0");
        calc.equal();
        assertEquals(test.getDisplay(), "NaN");
    }
    @Test (timeout = 1000)
    public void testExample4() {
        calc.inputDigit('1');
        calc.dot();
        calc.inputDigit('2');
        assertEquals(test.getDisplay(),"1.2");
        calc.dot();
        assertEquals(test.getInvalid(),true);
    }
    @Test (timeout = 1000)
    public void testExample5() {
        calc.delete();
        calc.delete();
        calc.delete();
        calc.delete();
        calc.inputDigit('9');
        calc.inputDigit('9');
        calc.operator('*');
        assertEquals(test.getDisplay(),"99 *");
        calc.operator('/');
        assertEquals(test.getDisplay(),"99 /");
        calc.inputDigit('6');
        calc.inputDigit('5');
        assertEquals(test.getDisplay(),"99 / 65");
        calc.operator('*');
        assertEquals(test.getInvalid(),true);
        calc.equal();
        assertEquals(test.getDisplay(),"1.52");
    }
    @Test (timeout = 1000)
    public void testDivideByZeroPos() {
        calc.inputDigit('1');
        calc.operator('/');
        calc.inputDigit('0');
        calc.equal();
        assertEquals(test.getDisplay(),"Infinity");
    }
}
/**
 * CS 180 Homework 02
 * It's a simple calculator; adds, subtracts, and multiplies
 * @author Ryan Everett, everettr@purdue.edu
 */
public class Calculator {
    int add(int x, int y) {
        return x+y;
    }
    int sub(int x, int y) {
        //y-x
        return x-y;
    }
    int mul(int x, int y) {
        return x*y;
    }
    static public void main(String[] args) {
        Calculator c = new Calculator();
        System.out.println(c.add(10, 20));
        System.out.println(c.sub(50, 25));
        System.out.println(c.mul(8, 8));
    }
}

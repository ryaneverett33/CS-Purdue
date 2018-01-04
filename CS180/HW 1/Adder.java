/**
 * CS 180 Homework 01
 * It's an adder, super simple
 * @author Ryan Everett, everettr@purdue.edu
 */
public class Adder {
    int addOne(int value) {
        return value+1;
    }
    public static void main(String[] args) {
        Adder a = new Adder();
        int x = 5;
        int y = a.addOne(x);
    }
}

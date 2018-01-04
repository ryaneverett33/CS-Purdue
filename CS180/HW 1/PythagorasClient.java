/**
 * Pythagoras Client
 * -brief description-
 * @author Ryan Everett, everettr@purdue.edu
 */
public class PythagorasClient {
    public static void main(String[] args) {
        Pythagoras p = new Pythagoras();
        int side1 = 3;
        int side2 = 4;
        double hypotenuse = p.getHypotenuse(side1, side2);
        System.out.println("Side 'a': " + side1);
        System.out.println("Side 'b': " + side2);
        System.out.println("Hypotenuse: " + hypotenuse);
    }
}

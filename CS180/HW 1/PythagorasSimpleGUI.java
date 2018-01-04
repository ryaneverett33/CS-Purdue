import javax.swing.JOptionPane;
/**
 * Pythagoras Simple GUI
 * -brief description-
 * @author Ryan Everett, everettr@purdue.edu
 */

public class PythagorasSimpleGUI {
    public static void main(String[] args) {
        Pythagoras p = new Pythagoras();
        String title = "Pythagoras GUI";
        String sideA = JOptionPane.showInputDialog(null,"Enter the length of side 'a': ",title,JOptionPane.QUESTION_MESSAGE);
        String sideB = JOptionPane.showInputDialog(null,"Enter the length of side 'b': ",title,JOptionPane.QUESTION_MESSAGE);
        int side1 = Integer.parseInt(sideA);
        int side2 = Integer.parseInt(sideB);
        double hypotenuse = p.getHypotenuse(side1, side2);
        JOptionPane.showMessageDialog(null,hypotenuse,"Hypotenuse: "+hypotenuse,JOptionPane.INFORMATION_MESSAGE);
        /*System.out.println("Side 'a': " + side1);
        System.out.println("Side 'b': " + side2);
        System.out.println("Hypotenuse: " + hypotenuse);*/
    }
}

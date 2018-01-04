/**
 * Created by Ryan on 9/16/2015.
 */
import java.util.*;
public class FAFSAClient {
    static public void main(String args[]) {
        Scanner scan = new Scanner(System.in);
        boolean isAcceptedStudent;
        boolean isSSregistered;
        boolean hasSSN;
        boolean hasValidResidency;
        boolean isDependent;
        int age;
        int creditHours;
        double studentIncome;
        double parentIncome;
        String classStanding;

        System.out.println("Have you been accepted into a degree or certificate program? Yes/No");
        String input1 = scan.nextLine();
        if (input1.equalsIgnoreCase("yes")) {
            isAcceptedStudent = true;
        } else {
            isAcceptedStudent = false;
        }
        System.out.println("Are you registered with Selective Service? Yes/No");
        String input2 = scan.nextLine();
        if (input2.equalsIgnoreCase("yes")) {
            isSSregistered = true;
        }
        else {
            isSSregistered = false;
        }
        System.out.println("Do you have a social security number? Yes/No");
        String input3 = scan.nextLine();
        if (input3.equalsIgnoreCase("yes")) {
            hasSSN = true;
        }
        else {
            hasSSN = false;
        }
        System.out.println("Do you have valid residency status? Yes/No");
        String input4 = scan.nextLine();
        if (input4.equalsIgnoreCase("yes")) {
            hasValidResidency = true;
        }
        else {
            hasValidResidency = false;
        }
        System.out.println("How old are you?");
        age = scan.nextInt();
        System.out.println("How many credit hours do you plan on taking?");
        creditHours = scan.nextInt();
        System.out.println("As a student, what is your total yearly income?");
        studentIncome = (double)scan.nextInt(); //scan.nextDouble() will probably work, let's not try it.
                                                //Upcasting int to a Double
        System.out.println("What is your parent's total yearly income?");
        parentIncome = (double)scan.nextInt();  //same as above declaration, upcast to double
        scan.nextLine();    //clear the input buffer
        System.out.println("Are you a dependent? Yes/No");
        String input5 = scan.nextLine();    //don't judge my variable names
        if(input5.equalsIgnoreCase("yes")) {
            isDependent = true;
        }
        else {
            isDependent = false;
        }
        System.out.println("Are you an undergraduate or graduate?");
        classStanding = scan.nextLine();
        FAFSA f = new FAFSA(isAcceptedStudent,isSSregistered,hasSSN,hasValidResidency,isDependent,age,creditHours,
                studentIncome,parentIncome,classStanding);
        System.out.println("Estimated total federal aid award: $" + f.calcFederalAidAmount());
    }
}

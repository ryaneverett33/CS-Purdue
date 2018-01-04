import javax.swing.*;
import javax.xml.ws.Holder;
import java.text.DecimalFormat;
import java.util.DoubleSummaryStatistics;

/**
 * Created by Ryan on 11/3/2015.
 */
public class FAFSAClient {
    public static void main(String args[]) {
        boolean alive = true;
        do {
            JOptionPane.showMessageDialog(null, "Welcome to the FAFSA!", "Message", JOptionPane.INFORMATION_MESSAGE);
            String[] certificateOptions = {"Yes", "No"};
            int degreeProgram = JOptionPane.showConfirmDialog(null,
                    "Have you been accepted into a degree or certificate program?",
                    "Program Acceptance",
                    JOptionPane.YES_NO_OPTION);
            int selService = JOptionPane.showConfirmDialog(null,
                    "Are you registered for the selective service?",
                    "Selective Service",
                    JOptionPane.YES_NO_OPTION);
            int ssNum = JOptionPane.showConfirmDialog(null,
                    "Do you have a social security number?",
                    "Social Security Number",
                    JOptionPane.YES_NO_OPTION);
            int resStatus = JOptionPane.showConfirmDialog(null,
                    "Do you have valid residency status?",
                    "Residency Status",
                    JOptionPane.YES_NO_OPTION);
            int age = -1;
            do {
                String STRINGage = JOptionPane.showInputDialog(null,
                        "How old are you?",
                        "Age",
                        JOptionPane.QUESTION_MESSAGE);
                try {
                    age = Integer.parseInt(STRINGage);
                    if (age < 0) {
                        JOptionPane.showMessageDialog(null,
                                "Age cannot be a negative number",
                                "Error: Age",
                                JOptionPane.ERROR_MESSAGE);
                    }
                } catch (Exception e) {   //Generic Exception is generic
                    System.out.println("Not a valid number");
                    JOptionPane.showMessageDialog(null,
                            "Not a valid number",
                            "Error: Age",
                            JOptionPane.ERROR_MESSAGE);
                }
            }
            while (age < 0);
            //It was at this moment, I realized this application had to be a do while. ugh
            int creditHours = -1;
            do {
                String STRINGhours = JOptionPane.showInputDialog(null,
                        "How many credits hours do you plan on taking?",
                        "Credit Hours",
                        JOptionPane.QUESTION_MESSAGE);
                try {
                    creditHours = Integer.parseInt(STRINGhours);
                    if (creditHours < 1 || creditHours > 24) {
                        JOptionPane.showMessageDialog(null,
                                "Credit hours must be between 1 and 24, inclusive",
                                "Error: Credit Hours",
                                JOptionPane.ERROR_MESSAGE);
                    }
                }
                catch (Exception e) {   //much generic
                    System.out.println("Not a valid number");
                    JOptionPane.showMessageDialog(null,
                            "Not a valid number",
                            "Error: Age",
                            JOptionPane.ERROR_MESSAGE);
                }
            }
            while (creditHours < 1 || creditHours > 24);
            double studentIncome = -1;    //kudos, if you have some
            do {
                String STRINGstudentIncome = JOptionPane.showInputDialog(null,
                        "What is your total yearly income?",
                        "Student Income",
                        JOptionPane.QUESTION_MESSAGE);
                try {
                    studentIncome = Double.parseDouble(STRINGstudentIncome);
                    if (studentIncome < 0) {
                        JOptionPane.showMessageDialog(null,
                                "Income cannot be a negative number",   //I disagree
                                "Error: Student Income",
                                JOptionPane.ERROR_MESSAGE);
                    }
                }
                catch (Exception e) {
                    System.out.println("Not a valid number");
                    JOptionPane.showMessageDialog(null,
                            "Not a valid number",
                            "Error: Age",
                            JOptionPane.ERROR_MESSAGE);
                }
            }
            while (studentIncome < 0);
            double parentIncome = -1;
            do {
                String STRINGparentIncome = JOptionPane.showInputDialog(null,
                        "What is your parent's total yearly income?",
                        "Parent Income",
                        JOptionPane.QUESTION_MESSAGE);
                try {
                    parentIncome = Double.parseDouble(STRINGparentIncome);
                    if (parentIncome < 0) {
                        JOptionPane.showMessageDialog(null,
                                "Income cannot be a negative number",
                                "Error: Parent Income",
                                JOptionPane.ERROR_MESSAGE);
                    }
                }
                catch (Exception e) {
                    System.out.println("Not a valid number");
                    JOptionPane.showMessageDialog(null,
                            "Not a valid number",
                            "Error: Age",
                            JOptionPane.ERROR_MESSAGE);
                }
            }
            while (parentIncome < 0);
            int dependent = JOptionPane.showConfirmDialog(null,
                    "Are you a dependent?",
                    "Dependency",
                    JOptionPane.YES_NO_OPTION);
            String[] classOptions = { "Freshman", "Sophmore", "Junior", "Senior" };
            String classPos = (String) JOptionPane.showInputDialog(null,
                    "What is your current class standing?",
                    "Class Standing",
                    JOptionPane.QUESTION_MESSAGE,
                    null,
                    classOptions,
                    null);
            //Do some parsing of data, because I'm lazy
            boolean isAcceptedStudent = false;
            boolean isSSregistered = false;
            boolean hasSSN = false;
            boolean hasValidResidency = false;
            boolean isDependent = false;
            if (degreeProgram == 0) {
                isAcceptedStudent = true;
            }
            if (selService == 0) {
                isSSregistered = true;
            }
            if (ssNum == 0) {
                hasSSN = true;
            }
            if (resStatus == 0) {
                hasValidResidency = true;
            }
            if (dependent == 0) {
                isDependent = true;
            }
            FAFSA f = new FAFSA(isAcceptedStudent, isSSregistered, hasSSN, hasValidResidency,
                    isDependent, age, creditHours, studentIncome, parentIncome, classPos);
            //For decimal formatting
            //http://www.javaprogrammingforums.com/java-programming-tutorials/
            //297-java-program-format-double-value-2-decimal-places.html
            DecimalFormat df = new DecimalFormat("#.##");
            double Dloans = f.calcStaffordLoan();
            double Dgrants = f.calcFederalGrant();
            double DworkStudy = f.calcWorkStudy();
            double Dtotal = f.calcFederalAidAmount();
            String loans = "Loans: $"+df.format(Dloans)+"\n";
            String grants = "Grants: $"+df.format(Dgrants)+"\n";
            String workStudy = "Work Study: $"+df.format(DworkStudy)+"\n";
            String spacer = "------------\n";
            String total = "Total: $"+df.format(Dtotal);
            JOptionPane.showMessageDialog(null,
                    loans+grants+workStudy+spacer+total,
                    "FAFSA Results",
                    JOptionPane.INFORMATION_MESSAGE);
            int doContinue = JOptionPane.showConfirmDialog(null,
                    "Would you like to complete another Application",
                    "Continue",
                    JOptionPane.YES_NO_OPTION,
                    JOptionPane.QUESTION_MESSAGE);
            if (doContinue == 1) {
                alive = false;
            }
        }
        while (alive);
    }
}

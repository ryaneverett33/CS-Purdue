/**
 * Created by Ryan on 9/16/2015.
 */
import java.util.*;
public class FAFSA {
    boolean isAcceptedStudent = false;
    boolean isSSregistered = false;
    boolean hasSSN = false;
    boolean hasValidResidency = false;
    boolean isDependent = false;
    int age = 0;
    int creditHours = 0;
    double studentIncome = 0;
    double parentIncome = 0;
    String classStanding = "";
    public FAFSA(boolean isAcceptedStudent, boolean isSSregistered, boolean hasSSN,
                 boolean hasValidResidency, boolean isDependent, int age,
                 int creditHours, double studentIncome, double parentIncome,
                 String classStanding) {
        this.isAcceptedStudent = isAcceptedStudent;
        this.isSSregistered = isSSregistered;
        this.hasSSN = hasSSN;
        this.hasValidResidency = hasValidResidency;
        this.isDependent = isDependent;
        this.age = age;
        this.creditHours = creditHours;
        this.studentIncome = studentIncome;
        this.parentIncome = parentIncome;
        /*if(classStanding == null) {
            this.classStanding = "";
        }*/
        this.classStanding = classStanding;
    }
    /**
     * Determines if the student is eligible for federal financial aid. To be
     * eligible, the student must be an accepted student to a higher education
     * program (isAcceptedStudent), must be registered with the selective service
     * (isSSregistered) if they are between  the ages of 18-25 inclusive, must
     * have a social security number (hasSSN), and must have valid residency
     * status (hasValidResidency).
     *
     * @return True if the student is aid eligible and false otherwise
     */
    public boolean isFederalAidEligible() {
        if(isAcceptedStudent && hasSSN && hasValidResidency) {
            if(age > 17 && age < 26)
            {
                if(isSSregistered) {
                    return true;
                }
                else if (!isSSregistered){
                    return false;
                }
                return false;
            }
            else {
                return true;
            }
        }
        else {
            return false;
        }
    }
    /**
     * Calculates the students expected family contribution. If the student is
     * a dependent, then their EFC is calculated by the sum of the students
     * income and their parent's income, else if it just the student's income.
     *
     * @return The students expected family contribution
     */
    public double calcEFC() {
        if(isDependent) {
            return studentIncome + parentIncome;
        }
        else {
            return studentIncome;
        }
    }
    /**
     * Calculates the student's federal grant award. The student's EFC must be
     * less than or equal to 50000 and they must be an undergraduate. The award
     * amount is based on their class standing and credit hours. Refer to the
     * tables in the breakdown section.
     *
     * @return The student's calculated federal grant award amount
     */
    public double calcFederalGrant() {
        if(isUndergraduate().equals("undergraduate") && (calcEFC() <= 50000)) {
            if (creditHours > 8) {
                return 5775;
            } else {
                return 2500;
            }
        }
        else if(isUndergraduate().equals(" ")) {
            return 0;
        }
        return 0;
    }
    /**
     * Calculates the student's total Stafford loan award. The Stafford loan is
     * only available for students registered for 9 or more credit hours. The amount
     * of the award is calculated by the student's dependency status and their
     * class standing. Refer to the tables in the breakdown section.
     *
     * @return The student's calculated Stafford loan award amount
     */
    public double calcStaffordLoan() {
        if(creditHours > 8) {
            if(isDependent) {
                if(isUndergraduate().equals("undergraduate")) {
                    return 5000;
                }
                else if (isUndergraduate().equals("graduate")) {
                    return 10000;
                }
            }
            else if(!isDependent){
                if(isUndergraduate().equals("undergraduate")) {
                    return 10000;
                }
                else if(isUndergraduate().equals("graduate")){
                    return 20000;
                }
            }
        }
        else if(creditHours < 8) {
            return 0;
        }
        return 0;
    }
    /**
     * Calculates the student's work study award. The work study award is
     * based on the student's EFC. Refer to the table in the breakdown section.
     *
     * @return The student's calculated federal grant award amount
     */
    public double calcWorkStudy() {
        if(calcEFC() <= 30000) {
            return 1500;
        }
        else if(calcEFC() <= 40000 && calcEFC() >= 30000.01) {
            return 1000;
        }
        else if(calcEFC() <= 50000 && calcEFC() >= 40000.0) {
            return 500;
        }
        else {
            return 0;
        }
    }
    /**
     * Calculates the student's total combined federal aid award. The total
     * aid award is calculated as the sum of Stafford loan award, federal grant
     * award, and work study award. You should make a call to the method
     * isFederalAidEligible() to see if the student is eligible to receive
     * federal aid. If they are NOT eligible, you can return 0. If the are, you
     * will return their total aid award.
     *
     * @return The student's total aid award amount
     */
    public double calcFederalAidAmount() {
        if(classStanding == null) {
            return 0;
        }
        if(age == 0) {
            return 0;
        }
        return calcFederalGrant() + calcStaffordLoan() + calcWorkStudy();
    }
    public String isUndergraduate() {
        // Example 1
        if (classStanding == null || classStanding.equals(null) || classStanding.equals("null")) {
            return " ";
        }
        else if (classStanding.equalsIgnoreCase("UnDerGradUAtE")) {
            return "undergraduate";
        }
        else if (classStanding.equalsIgnoreCase("graduate")) {
            return "graduate";
        }
        else {
            return " ";
        }
    }
}

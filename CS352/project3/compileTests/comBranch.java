// A complicated test of boolean binary arithmetic
class comBranch {
    public static void main(String[] args) {
        if (true || false || (true && (!false))) {
            System.out.println("True");
        }
        else {
            System.out.println("False");
        }
    }
}
class nestedBranch {
    public static void main(String[] args) {
        if (true || false) {
            if (1==1) {
                System.out.println("success");
            }
            else {
                System.out.println("failed2");
            }
        }
        else {
            System.out.println("failed");
        }
    }
}
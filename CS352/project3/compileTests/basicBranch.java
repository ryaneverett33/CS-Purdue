class basicBranch {
    public static void main(String[] args) {
        if (true) {
            if (!true) {
                System.out.println("Nested true");
            }
            else {}
        }
        else {
            System.out.println("Resulted in false");
        }
    }
}
class bool {
    public static void main(String[] args) {
        {
            if (true && true) {
                System.out.println("true1");
            }
            else {
                System.out.println("false1");
            }
            if ((1==1) && (3==3)) {
                System.out.println("true2");
            }
            else {
                System.out.println("false2");
            }
            if ((1==1) && true) {
                System.out.println("true3");
            }
            else {
                System.out.println("false3");
            }
        }
    }
}
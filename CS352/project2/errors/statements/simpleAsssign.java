class Main {
    public static void main (String[] args) {
        System.out.println(new Assign().run());
    }
}
class Assign {
    boolean b;
    public int run() {
        b = 1;
        return 1;
    }
}
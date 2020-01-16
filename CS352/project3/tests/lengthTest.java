class Main {
    public static void main (String[] args) {
        {
            System.out.println(new Test().test());
            System.out.println(new Test().test2());
        }
    }
}
class Test {
    boolean[] b;
    boolean[][] b2;
    public int test() {
        b = new boolean[5];
        return b.length;
    }
    public int test2() {
        b2 = new boolean[5][3];
        return b2[0].length;
    }
}
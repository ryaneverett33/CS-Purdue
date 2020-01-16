class arrayGet {
    public static void main(String[] args) {
        System.out.println(new Arr().run());
    }
}
class Arr {
    public int run() {
        int[] b;
        b = new int[5];
        b[0] = 5+5;
        b[1+0] = 6+4;
        System.out.println(b[1]);
        return b[0];
    }
}
class Main {
    public static void main (String[] args) {
        System.out.println(new Test().setup());
    }
}
class Test {
    int b;
    public int setup() {
        return b.length;
    }
}
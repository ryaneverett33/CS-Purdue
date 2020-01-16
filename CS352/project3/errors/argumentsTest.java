class argumentsTest {
    public static void main (String[] args) {
        System.out.println(new Test().run(69, 1));
    }
}
class Test {
    public int run(int a, boolean five) {
        if (five)
            System.out.println("Five is true");
        else
            System.out.println("Five is false");
        return a;
    }
}
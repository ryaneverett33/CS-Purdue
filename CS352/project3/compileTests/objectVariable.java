class objectVariable {
    public static void main (String[] args) {
        System.out.println(new B().run());
    }
}
class A {}
class B {
    public int run() {
        B b;
        b = new B();
        return 1;
    }
}
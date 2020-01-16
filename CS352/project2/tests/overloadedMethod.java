class Test {
    public static void main (String[] args) { {
        System.out.println(new A().doSomething());
        System.out.println(new A().doSomething(5));
    }
    }
}
class A {
    public int doSomething() {
        return 0;
    }
    public int doSomething(int a) {
        return a;
    }
}
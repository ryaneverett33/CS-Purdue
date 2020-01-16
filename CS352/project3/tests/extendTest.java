class Test {
    public static void main (String[] args) {
        {
            System.out.print("Do something in A (class A): ");
            System.out.println(new A().doSomethingInA());
            System.out.print("Do something in B (class B): ");
            System.out.println(new B().doSomethingInB());
            System.out.print("Do something in A (class B): ");
            System.out.println(new B().doSomethingInA());
        }
    }
}
class A {
    public int doSomethingInA() {
        return 7;
    }
}
class B extends A {
    public int doSomethingInB() {
        return 5;
    }
}
class Basic {
    public static void main(String[] a) {
        {
            System.out.println("Running test");
            System.out.println(new ComputeRunner().run());
        }
    }
}
class ComputeRunner {
    boolean hello;
    public int run() {
        Compute compute;
        compute = new Compute();
        System.out.println(compute.setup());
        System.out.println(compute.printValues());
        System.out.println(compute.setValues(10,1));
        System.out.println(compute.printValues());
        System.out.print("Add: ");
        System.out.println(compute.add());
        System.out.print("Subtract: ");
        System.out.println(compute.subtract());
        System.out.print("Special: ");
        System.out.println(compute.special());
        return 1;
    }
}
class Compute {
    int a;
    int b;

    public int setup() {
        a = 5;
        b = 6;
        return 0;
    }
    public int setValues(int c, int d) {
        a = c;
        b = d;
        return 0;
    }
    public int add() {
        return a + b;
    }
    public int subtract() {
        return a - b;
    }
    public int special() {
        return this.add() - this.subtract();
    }
    public int printValues() {
        System.out.print("Compute values are: ");
        System.out.print(a);
        System.out.print(", ");
        System.out.print(b);
        System.out.println(" ");
        return 0;
    }
}
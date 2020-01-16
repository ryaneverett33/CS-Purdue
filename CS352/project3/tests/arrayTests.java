class Test {
    public static void main (String[] a) {
        {
            System.out.println(new Runner().run());
        }
    }
}
class Runner {
    public int run() {
        arguments a;
        returner r;
        int[] arr;
        boolean[] hello;
        a = new arguments();
        r = new returner();
        arr = new int[5];
        System.out.println(a.size(arr));
        hello = r.make(5);
        System.out.println(hello.length);
        return 0;
    }
}
class arguments {
    public int size(int[] a) {
        return a.length;
    }
}
class returner {
    boolean[] arr;
    public boolean[] make(int size) {
        arr = new boolean[5];
        return arr;
    }
}
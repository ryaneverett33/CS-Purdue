class recursiveTest {
    public static void main(String[] a) {
        System.out.println(new Recurse().recurse(5));
    }
}
class Recurse {
    public int recurse(int x) {
        if (x < 3)
            return x;
        else
            return this.recurse(x-1);
        return 0;
    }
}
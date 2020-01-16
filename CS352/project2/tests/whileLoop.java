class whileLoop {
    public static void main(String[] args) {
        System.out.println(new Test().loop());
    }
}
class Test {
    int i;
    public int loop() {
        i = 0;
        while (i < 5) {
            i = i + 1;
        }
        return i;
    }
}
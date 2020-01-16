class nestedWhile {
    public static void main(String[] args) {
        System.out.println(new Obj().run());
    }
}
class Obj {
    int i;
    public int run() {
        int j;
        j = 0;
        i = 0;
        while (j < 5) {
            while (i < 5) {
                i = i + 1;
            }
            j = j + 1;
        }
        return i * j;
    }
}
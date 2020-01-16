class nestedCall {
    public static void main(String[] args) {
        System.out.println(new Runner().run());
    }
}
class Something {
    public int method() {
        return 69;
    }
}
class Runner {
    public int run() {
        Something something;
        something = new Something();
        return something.method();
    }
}
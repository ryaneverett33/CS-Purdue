class basic {
    public static void main(String[] args) { {
        System.out.println(new Obj().run());
        System.out.println(new Obj().run2(69));
    }
        
    }
}
class Obj {
    public int run() {
        return 1;
    }
    public int run2(int x) {
        return x;
    }
}
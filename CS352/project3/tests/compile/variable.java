class variable {
    public static void main(String[] args) {
        System.out.println(new Obj().run(5));
    }
}
class Obj {
    int x;
    public int run(int newX) {
        x = newX;
        return x;
    }
}
/*
main:
    v1 <- NEW Obj
    push 5
    v2 <- v1 CALL run
Obj_run:
    v1 <- newX
    x <- v1
    v1 <- pop x
    return v1
*/
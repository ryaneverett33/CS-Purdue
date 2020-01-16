class whileLoop {
    public static void main (String[] args) {
        System.out.println(new Obj().run());
    }
}

class Obj {
    public int run() {
        int x;
        x = 0;
        while (x < 5) {
            x = x + 1;
        }
        return x;
    }
}
/*
main:
    v1 <- new Obj
    v2 <- v1 call run
    PRINTLN v2
obj_run
    x <- 0
    MARK
    v1 <- x
    v1 <- v1 < 5
    if v1 goto obj_run_b0
    v1 <- x
    return v1
obj_run_b0
    v1 <- x
    v1 <- v1 + 1
    x <- v1
    GOBACK
*/
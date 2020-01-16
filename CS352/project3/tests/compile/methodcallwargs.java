class methodcwargs {
    public static void main (String[] args) {
        System.out.println(new Obj().add(1,2));
    }
}
class Obj {
    int a;
    int b;
    public int add(int x, int y) {
        int c;
        int d;
        return x + y;
    }
}
/*
main:
	v1 <- new Obj
	push 1
	push 2
	v2 <- v1 call add
	PRINTLN v2
Obj_add:
	y <- pop
	x <- pop
    v1 <- x + y
	return v1
*/
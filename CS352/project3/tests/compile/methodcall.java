class methodcall {
    public static void main (String[] args) {
        System.out.println(new Obj().doSomething());
    }
}
class Obj {
    public int doSomething() {
        return 1;
    }
}
/*
main:
	v1 <- new Obj
	v2 <- v1 call doSomething
	PRINTLN v2
Obj_doSomething:
	return 1
*/
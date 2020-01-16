class array {
    public static void main(String[] a) { {
        System.out.println(new Obj().len(5));
        System.out.println(new Obj().index());
    }
        
    }
}
class Obj {
    int[] arr;
    public int len(int x) {
        arr = new int[x];
        return arr.length;
    }
    public int index() {
        arr = new int[5];
        arr[0] = -1;
        arr[1] = 7;
        return arr[0];
    }
}
/*
main:
    v1 <- new Obj
    push 5
    v2 <- v1 call length
    PRINTLN v2
    v1 <- new Obj
    v2 <- v1 call index
    PRINTLN v2
obj_length:
    v1 <- new int
    v2 <- pop x
    v1 <- ARR v2
    arr <- v1
    v1 <- arr
    v1 <- LENGTH v1
    return v1
obj_index:
    v1 <- new int
    v1 <- ARR 5
    arr <- v1
    v1 <- arr
    v1 <- ARR 0
    v1 <- STORE -1
    v1 <- arr
    v1 <- ARR 1
    v1 <- STORE 7
    v1 <- arr
    v1 <- ARR 0
    v1 <- GET
    return v1
*/
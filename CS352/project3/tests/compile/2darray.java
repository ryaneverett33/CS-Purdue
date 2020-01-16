class array {
    public static void main(String[] args) { {
        System.out.println(new Obj().getLength(5,6));
        System.out.println(new Obj().setAndGet(5));
    }
        
    }
}
class Obj {
    boolean[][] arr;
    int[][] arr2;
    public int getLength(int x, int y) {
        arr = new boolean[x][y];
        return arr[0].length;
    }
    public int setAndGet(int value) {
        arr2 = new int[2][2];
        arr2[0][1] = value;
        return arr2[0][1];
    }
}

/*
main:
    v1 <- new Obj
    push 5
    push 6
    v2 <- v1 call getLength
    PRINTLN v2
Obj_getLength:
    v1 <- x
    v2 <- y
    v3 <- new BOOLEAN
    v3 <- ARR v1 v2
    arr <- v3
    v1 <- arr
    v1 <- ARR 0
    v1 <- LENGTH v1
    return v1
Obj_setAndGet:
    v1 <- new int
    v1 <- ARR 2 2
    arr2 <- v1
    v1 <- arr2
    v1 <- ARR 0 1
    v2 <- value
    v1 <- STORE value
    v1 <- arr2
    v1 <- ARR 0 1
    v1 <- GET
    return v1
*/

class IndexTest {
    public static void main (String[] args) { {
        System.out.println(new Test().test());
        System.out.println(new Test().test2());
    }
        
    }
}
class Test {
    int[] arr;
    int[][] arr2;
    public int test() {
        arr = new int[5];
        arr2 = new int[5][5];
        arr[0] = 1;
        System.out.println(arr[0]);
        System.out.println(arr2[0][0]);
        return 0;
    }
    public int test2() {
        arr2 = new int[5][5];
        System.out.println(arr2[0].length);
        return 0;
    }
}
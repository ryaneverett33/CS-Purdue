class basicArray {
    public static void main(String[] args) {
        System.out.println(new Test().run());
    }
}
class Test {
    int[] arr;
    int[][] arr2;
    boolean[] boolArr;
    public int run() {
        int i;
        i = 0;
        arr = new int[5];
        arr2 = new int[2][2];
        boolArr = new boolean[2];
        arr[0] = 50;
        arr2[1][1] = 200;
        boolArr[0] = true;
        boolArr[1] = false;
        System.out.print(arr[0]);
        System.out.print(", ");
        System.out.print(arr2[1][1]);
        System.out.print(", ");
        System.out.print(arr2[0][0]);
        System.out.print("\n");
        while (boolArr[i]) {
            System.out.println("Bool Arr is True");
            i = i +1;
        }
        return 5;
    }
}
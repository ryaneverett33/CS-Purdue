class Main {
    public static void main (String[] a) {
        System.out.print(new Test().run());
    }
}
class Test {
    int[][] arr;
    public int run() {
        arr = new int[5][5];
        arr[0][0] = 5;
        arr[3][3] = 3;
        System.out.println(arr[0][0]);
        System.out.println(arr[3][3]);
        return -1;
    }
}
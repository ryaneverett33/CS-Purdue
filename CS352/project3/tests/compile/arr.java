class arr {
    public static void main(String[] args) {
        System.out.println(new Obj().run());
    }
}
class Obj {
    int x;
    public int run() {
        int[][] arr;
        x = 0;
        arr = new int[5][5];
        arr[3][2] = 5;
        return arr[3][2];
    }
}
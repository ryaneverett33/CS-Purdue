class basiCCALL {
    public static void main (String[] args) {
        System.out.println(new Caller().call(1));
    }
}
class Caller {
    public int call(int x) {
        return x;
    }
}
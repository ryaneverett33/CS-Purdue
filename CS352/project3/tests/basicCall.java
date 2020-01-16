class basiCCALL {
    public static void main (String[] args) {
        System.out.println(new Caller().call());
    }
}
class Caller {
    public int call() {
        return 1;
    }
}
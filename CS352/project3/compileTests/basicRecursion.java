class basicRecursion {
    public static void main(String[] args) {
        System.out.println(new Runner().recurse(4));
    }
}
class Runner {
    public int recurse(int i) {
        if (i < 2) {
            return i; 
        }
        else {
            return this.recurse(i-1);
        }
        return 0;
    }
}
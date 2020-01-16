class vars {
    public static void main(String[] args) {
        System.out.println(new Obj().run());
    }
}
class Obj {
    int a;
    public int run() {
        //a = 0;
        //a = 1 + a;                  //IntExp[4]:1
        //a = a + a;                  //ExpBasic[5]:0
        //a = (a+a)+a;                //ExpNest[6]:1
        //a = ((a+a)+a)+a;
        //a = (a+a)+(a+a);            //ExpTwoNest[7]:0
        a = ((a+a)+(a+a))+(a+a);    //ExpDoubleNested[8]:2
        a = ((a+a)+(a+a))+((a+a)+(a+a));
        return a;
    }
}
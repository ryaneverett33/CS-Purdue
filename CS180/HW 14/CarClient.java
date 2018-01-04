/**
 * Created by Ryan on 10/16/2015.
 */
public class CarClient {
    public static void main(String args[]) {
        Car c = new Car(10);
        try {
            c.drive(300);
        } catch (InsufficientFuelException e) {
            System.out.println(e.getMessage()); //prints "Fuel too low!"
        }
        try {
            c.drive(200);
            System.out.println("Success");
        } catch (InsufficientFuelException e) {
            System.out.println(e.getMessage()); //prints "Fuel too low!"
        }
    }
}

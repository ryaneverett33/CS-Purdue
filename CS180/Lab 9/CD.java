/**
 * Created by Ryan on 10/21/2015.
 */
public class CD extends Product.AudioProduct {
    double price;
    CD(String productName, int totalSongs, double price) {
        super(productName, totalSongs);
        this.price = price;
    }
    public double getPrice() {
        return this.price;
    }
}

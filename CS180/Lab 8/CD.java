/**
 * Created by Ryan on 10/14/2015.
 */
public class CD implements Sellable {
    String productName;
    int totalSongs;
    double price;
    public CD(String productName, int totalSongs, double price) {
        this.productName = productName;
        this.totalSongs = totalSongs;
        this.price = price;
    }
    public String getProductName() {
        return this.productName;
    }
    public double getPrice() {
        return this.price;
    }
    public int getTotalSongs() {
        return this.totalSongs;
    }
}

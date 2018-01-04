/**
 * Created by Ryan on 10/14/2015.
 */
public class DVD implements Sellable {
    String productName;
    VideoType type;
    double price;

    public DVD(String productName, VideoType type, double price) {
        this.productName = productName;
        this.type = type;
        this.price = price;
    }
    public String getProductName() {
        return this.productName;
    }
    public double getPrice() {
        return this.price;
    }
    public VideoType getType() {
        return this.type;
    }
}

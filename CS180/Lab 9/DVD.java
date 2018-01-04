/**
 * Created by Ryan on 10/21/2015.
 */
public class DVD extends Product.VideoProduct {
    double price;
    DVD(String productName, VideoType type, double price) {
        super(productName, type);
        this.price = price;
    }
    public double getPrice() {
        return price;
    }
}

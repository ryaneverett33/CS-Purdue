/**
 * Created by Ryan on 10/14/2015.
 */
import java.util.UUID;
public class MP3 implements Sellable, Downloadable {
    String productName;
    public MP3(String productName) {
        this.productName = productName;
    }
    public String getProductName() {
        return this.productName;
    }
    public double getPrice() {
        return 0.99;
    }
    public String generateDownloadCode() {
        return UUID.randomUUID().toString();
    }
}

import java.util.UUID;

/**
 * Created by Ryan on 10/21/2015.
 */
public class MP3 extends Product.AudioProduct implements Downloadable{
    public MP3(String productName) {
        super(productName, 1);
    }
    public double getPrice() {
        return 0.99;
    }
    public String generateDownloadCode() {
        return UUID.randomUUID().toString();
    }
}

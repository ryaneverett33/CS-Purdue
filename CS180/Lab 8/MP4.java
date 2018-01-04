/**
 * Created by Ryan on 10/14/2015.
 */
import java.util.UUID;
public class MP4 implements Sellable, Downloadable {
    String productName;
    VideoType type;

    public MP4(String productName, VideoType type) {
        this.productName = productName;
        this.type = type;
    }
    public String getProductName() {
        return this.productName;
    }
    public double getPrice() {
        if(type == VideoType.MOVIE) {
            return 4.99;
        }
        else {
            return 19.99;
        }
    }
    public String generateDownloadCode() {
        return UUID.randomUUID().toString();
    }
    public VideoType getType() {
        return this.type;
    }
}

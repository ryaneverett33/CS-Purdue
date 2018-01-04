import java.util.UUID;

/**
 * Created by Ryan on 10/21/2015.
 */
public class MP4 extends Product.VideoProduct implements Downloadable {
    public MP4(String productName, VideoType type) {
        super(productName, type);
    }
    public double getPrice() {
        if (type == VideoType.MOVIE) {
            return 4.99;
        }
        else if (type == VideoType.TVSERIES) {
            return 19.99;
        }
        else {
            return 0;
        }
    }
    public String generateDownloadCode() {
        return UUID.randomUUID().toString();
    }
}

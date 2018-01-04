/**
 * Created by Ryan on 10/21/2015.
 */
public abstract class Product {
    String productName;

    public Product(String productName) {
        this.productName = productName;
    }

    String getProductName() {
        return this.productName;
    }

    //public abstract method that gets the price of this Product
    public abstract double getPrice();

    public static abstract class AudioProduct extends Product {
        int totalSongs;

        public AudioProduct(String productName, int totalSongs) {
            super(productName);
            this.totalSongs = totalSongs;
        }

        int getTotalSongs() {
            return totalSongs;
        }
    }

    public static abstract class VideoProduct extends Product {
        VideoType type;

        public VideoProduct(String productName, VideoType type) {
            super(productName);
            this.type = type;
        }
        VideoType getType() {
            return this.type;
        }
    }
}
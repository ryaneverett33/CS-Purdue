import java.awt.*;

/**
 * Created by Ryan on 11/18/2015.
 */
public class BetterRectangle extends Rectangle {
    public BetterRectangle(int x, int y, int width, int height) {
        super(x, y, width, height);
    }

    public double getPerimeter() {
        double widths = width * 2;
        double heights = height * 2;
        return widths + heights;
    }

    public double getArea() {
        return width * height;
    }
}

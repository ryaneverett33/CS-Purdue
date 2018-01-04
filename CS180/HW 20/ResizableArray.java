/**
 * Created by Ryan on 12/1/2015.
 */
public class ResizableArray {
    int[] array;
    int size;

    public ResizableArray() {
        array = new int[4];
        size = 0;
    }
    public void add(int value) {
        if (size < array.length) {
            array[size] = value;
            size++;
        }
        else if (size == array.length) {
            int[] tmp = new int[array.length * 2];
            for (int i = 0; i < array.length; i++) {
                tmp[i] = array[i];
            }
            array = tmp;
            array[size] = value;
            size++;
        }
    }
    public int getSize() {
        return this.size;
    }
    public int getArraySize() {
        return array.length;
    }
    //returns a string representing the values added
    //to the array with a comma after each value.
    public String toString() {
        String tmp = "";
        for (int i = 0; i < size; i++) {
            String foo = array[i] + ",";
            tmp = tmp + foo;
        }
        return tmp;
    }
}

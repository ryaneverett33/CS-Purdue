/**
 * The MusicStore class models a Music Store where you can add, remove, or get products and sort them
 * by price in ascending or descending order.
 */
import java.util.Arrays;
public class MusicStore {
    private int totalProducts;
    private int maxProducts;
    private Sellable[] storeProducts;

    /**
     * Constructor. Initializes this MusicStore with 0 products, a max capacity of 10 products, and
     * an empty array of Sellable products of size 10.
     */
    public MusicStore() {
        maxProducts = 10;
        totalProducts = 0;
        storeProducts = new Sellable[maxProducts];
}

    /**
     * Adds the specified Sellable product to this MusicStore. If the product already exists, then
     * the method returns false and no changes are made. If the product does not already exist, a check
     * is made if the totalProducts is equal to the maxProducts and the array capacity is double if
     * needed before the new product is added.
     *
     * @param product The Sellable product to add to this MusicStore
     * @return true if the product was added, false otherwise
     */
    public boolean addProduct(Sellable product) {
        //If it contains it, return false.
        if (contains(product) || product == null) {
            return false;
        }
        else {
            if (totalProducts == maxProducts) {
                maxProducts = maxProducts * 2;
                //Resize that baby
                Sellable[] x = new Sellable[maxProducts];
                for (int i = 0; i < storeProducts.length; i++) {
                    x[i] = storeProducts[i];
                }
                storeProducts = x;
            }
            storeProducts[totalProducts] = product;
            totalProducts++;
            return true;
        }
    }

    /**
     * Removes the product given by the name argument from this MusicStore and moves all products that
     * follow it in the storeProducts array to the left so that there are no empty entries between
     * products. For example:
     *
     * before -> {S1, S2, S3, S4, S5, S6, S7, S8, S9, null}
     * remove S6
     * after -> {S1, S2, S3, S4, S5, S7, S8, S9, null, null}
     *
     * @param name The name of the product to remove from this MusicStore
     * @return true if the product was removed, false otherwise
     */
    public boolean removeProductByName(String name) {
        if (!contains(name) || name == null) {
            return false;
        }
        //Since storeProducts contains the product, we can continue
        int index = getProductIndex(name);
        boolean skip = false;   //Set to true when we reach the value we don't want
        Sellable[] newSellables = new Sellable[storeProducts.length - 1];
        for (int i = 0; i < storeProducts.length - 1; i++) {
            if (i == index) {
                skip = true;
            }
            if (skip) {
                newSellables[i] = storeProducts[i + 1];
            } else if (!skip) {
                newSellables[i] = storeProducts[i];
            }
        }
        totalProducts--;
        storeProducts = newSellables;
        return true;
    }

    /**
     * Gets the product from the list of Sellable products of this MusicStore by the given name.
     *
     * @param product The name of the product to get
     * @return The product with the given name, or null if the product is not found
     */
    public Sellable getProductByName(String product) {
        if (!contains(product) || product == null) {
            return null;
        }
        int index = getProductIndex(product);
        return storeProducts[index];
    }

    private int getProductIndex(String name) {
        //Referenced by removeProductByName and getProductByName
        //So I'm not crazy
        for (int i = 0; i < storeProducts.length; i++) {
            if (storeProducts[i].getProductName().equalsIgnoreCase(name)) {
                return i;
            }
        }
        return -1;
    }
    /**
     * Sorts all the Sellable products in this MusicStore by price. The ascending argument
     * specifies if the the products should be sorted in ascending or descending order. You
     * are free to use whichever sorting algorithm you choose from any outside resources
     * as long as the storeProducts array is sorted correctly as specified by the argument.
     *
     * @param ascending True to sort ascending by price, false to sort descending by price
     */
    public void sortAllProductsByPrice(boolean ascending) {
        //I can't use Arrays.sort and I am sad
        //Using the bubbleSort algorithm from https://en.wikipedia.org/wiki/Bubble_sort
        int n = totalProducts;
        boolean swapped = true;   //if the sorted array passes the test, we stop looping
        System.out.println("gonna sort");
        if (totalProducts != 0) {
            if (ascending == true) {
                System.out.println("is true");
                while (swapped) {
                    swapped = false;
                    for (int i = 1; i < n; i++) {
                        if (storeProducts[i-1].getPrice() > storeProducts[i].getPrice()) {
                            //FIX SWAP
                            storeProducts[i-1] = storeProducts[i];
                            storeProducts[i] = storeProducts[i-1];
                            swapped = true;
                            System.out.println("Swapped");
                        }
                        System.out.println("Not Swapped");
                    }
                }
            }
            else if (ascending == false) {
                System.out.println("is false");
                while (swapped) {
                    swapped = false;
                    for (int i = 1; i < n; i++) {
                        if (storeProducts[i-1].getPrice() < storeProducts[i].getPrice()) {
                            storeProducts[i-1] = storeProducts[i];
                            storeProducts[i] = storeProducts[i-1];
                            swapped = true;
                            System.out.println("Swapped");
                        }
                        System.out.println("Not Swapped");
                    }
                }
            }
        }

    }

    /**
     * Checks if a given Sellable product is already in this MusicStore.
     *
     * @param product The product to find
     * @return true if the product is found, false otherwise
     */
    private boolean contains(Sellable product) {
        if (storeProducts.length == 0) {
            return false;
        }
        for (Sellable s : storeProducts) {
            if(s == null) {
                return false;
            }
            if (s.equals(product)) {
                return true;
            }
        }
        return false;
    }


    /**
     * Checks if a Sellable product with the given name is already in this MusicStore.
     *
     * @param name The name of the product to find
     * @return true if the product is found, false otherwise
     */
    private boolean contains(String name) {
        //Also this method is eerily similar to contains, hmmmm
        if (storeProducts.length == 0) {
            return false;
        }
        for (Sellable s : storeProducts) {
            if(s == null) {
                return false;
            }
            //Oh my, differences in code
            if (s.getProductName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Prints all the products in this MusicStore. This method is complete and should not be modified.
     */
    public void printProducts() {
        for (int i = 0; i < this.totalProducts; i++) {
            Sellable temp = this.storeProducts[i];
            if (temp instanceof CD) {
                System.out.printf("CD Name:\t%s%n", temp.getProductName());
                System.out.printf("Total Songs:\t%d%n", ((CD) temp).getTotalSongs());
                System.out.printf("Price:\t\t%.2f%n", temp.getPrice());
            } else if (temp instanceof DVD) {
                System.out.printf("DVD Name:\t%s%n", temp.getProductName());
                System.out.printf("Type:\t\t%s%n", ((DVD) temp).getType());
                System.out.printf("Price:\t\t%.2f%n", temp.getPrice());
            } else if (temp instanceof MP3) {
                System.out.printf("MP3 Name:\t%s%n", temp.getProductName());
                System.out.printf("Price:\t\t%.2f%n", temp.getPrice());
            } else {
                System.out.printf("MP4 Name:\t%s%n", temp.getProductName());
                System.out.printf("Type:\t\t%s%n", ((MP4) temp).getType());
                System.out.printf("Price:\t\t%.2f%n", temp.getPrice());
            }
            System.out.println();
        }
    }
}


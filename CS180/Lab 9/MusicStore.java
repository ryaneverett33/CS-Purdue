/**
 * The MusicStore class models a Music Store where you can add, remove, or get products and sort them
 * by price in ascending or descending order.
 */
public class MusicStore {
    private int totalProducts;
    private int maxProducts;
    private Product[] storeProducts;
	
    /**
     * Constructor. Initializes this MusicStore with a capacity of 10 products.
     */
    public MusicStore() {
        this.maxProducts = 10;
		this.totalProducts = 0;
		storeProducts = new Product[maxProducts];
    }
	
    /**
     * Adds the specified Product product to this MusicStore. If the product already exists, then 
     * the method returns false and no changes are made. If the product does not already exist, a check
     * is made if the totalProducts is equal to the maxProducts and the array capacity is double if
     * needed before the new product is added.
     * 
     * @param product The Product product to add to this MusicStore
     * @return true if the product was added, false otherwise
     */
    public boolean addProduct(Product product) {
	if (contains(product)) {
            return false;
	}
	if (this.totalProducts == this.maxProducts) {
	    this.maxProducts *= 2;
	    Product[] temp = new Product[this.maxProducts];
	    for (int i = 0; i < this.totalProducts; i++) {
		temp[i] = this.storeProducts[i];
	    }
	    this.storeProducts = temp;
	}
	this.storeProducts[this.totalProducts++] = product;
	return true;
    }
	
    /**
     * Removes the product given by name identifier from this MusicStore and moves all products that 
     * follow it in the storeProducts array to the left so that there are no empty entries between
     * products. For example:
     * 
     * before -> {S1, S2, S3, S4, S5, S6, S7, S8, S9, null}
     * remove S6
     * after -> {S1, S2, S3, S4, S5, S7, S8, S9, null, null}
     * 
     * @param product The product to remove from this MusicStore
     * @return true if the product was removed, false otherwise
     */
    public boolean removeProductByName(String product) {
	if (contains(product)) {
	    for (int i = 0; i < this.totalProducts; i++) {
		if (this.storeProducts[i].getProductName().equals(product)) {
		    for (int j = i; j < this.totalProducts - 1; j++) {
			this.storeProducts[j] = this.storeProducts[j + 1];
		    }
		    this.storeProducts[this.totalProducts - 1] = null;
		    this.totalProducts--;
		    return true;
		}
	    }
	    return true;
        }
	return false;
    }
	
    /**
     * Gets the product from the list of Product products of this MusicStore by the given name.
     * 
     * @param product The name of the product to get
     * @return The product with the given name, or null if the product is not found
     */
    public Product getProductByName(String product) {
	for (int i = 0; i < this.totalProducts; i++) {
    	    if (this.storeProducts[i].getProductName().equals(product)) {
		return this.storeProducts[i];
	    }
	}
	return null;
    }
	
    /**
     * Sorts all the Product products in this MusicStore by price. The ascending argument
     * specifies if the the products should be sorted in ascending or descending order.
     * 
     * @param ascending True to sort ascending by price, false to sort descending by price
     */
    public Product[] sortAllProductsByPrice(boolean ascending) {
	boolean sorted = false;
	while (!sorted) {
	    sorted = true;
	    for (int i = 0; i < this.totalProducts - 1; i++) {
		double difference = this.storeProducts[i].getPrice() - this.storeProducts[i + 1].getPrice();
		if ((ascending && difference > 0) || (!ascending && difference < 0)) {
		    Product temp = this.storeProducts[i];
		    this.storeProducts[i] = this.storeProducts[i + 1];
		    this.storeProducts[i + 1] = temp;
		    sorted = false;
		}
	    }
	}
	return this.storeProducts;
    }
	
    /**
     * Filters the products in this store for only audio or video products by the specified argument.
     * 
     * @param audio true to filter audio products, false to filter video products
     */
    public Product[] filterAudioOrVideo(boolean audio) {
	Product[] filteredProducts = new Product[this.totalProducts];
	int filteredCount = 0;
	if (audio) {
		for (int i = 0; i < this.totalProducts; i++) {
			if (storeProducts[i] instanceof Product.AudioProduct) {
				filteredProducts[filteredCount] = storeProducts[i];
				filteredCount++;
			}
		}
	}
	else {
		for (int i = 0; i < this.totalProducts; i++) {
			if (storeProducts[i] instanceof Product.VideoProduct) {
				filteredProducts[filteredCount] = storeProducts[i];
				filteredCount++;
			}
		}
	}
	return filteredProducts;
    }
	
    /**
     * Filters the products in this store for only downloadable or non-downloadable products by the specified argument.
     * 
     * @param downloadable
     */
    public Product[] filterDownloadable(boolean downloadable) {
    	Product[] filteredProducts = new Product[this.totalProducts];
		int filteredCount = 0;
		if (downloadable) {
			for (int i = 0; i < this.totalProducts; i++) {
				if (storeProducts[i] instanceof Downloadable) {
					filteredProducts[filteredCount] = storeProducts[i];
					filteredCount++;
				}
			}
		}
		else {
			for (int i = 0; i < this.totalProducts; i++) {
				if (!(storeProducts[i] instanceof Downloadable)) {
					filteredProducts[filteredCount] = storeProducts[i];
					filteredCount++;
				}
			}
		}

	return filteredProducts;
    }
	
    /**
     * Gets a list of the Products in this MusicStore.
     * 
     * @return The list of Products in this MusicStore
     */
    public Product[] getProductsList() {
	return this.storeProducts;
    }
	
    /**
     * Checks if a given Product product is already in this MusicStore.
     * 
     * @param product The product to find
     * @return true if the product is found, false otherwise
     */
    private boolean contains(Product product) {
	for (int i = 0; i < this.totalProducts; i++) {
	    if (this.storeProducts[i].getProductName().equals(product.getProductName())) {
		return true;
	    }
	}
	return false;
    }
	
    /**
     * Checks if a given Product product is already in this MusicStore.
     * 
     * @param name The name of the product to find
     * @return true if the product is found, false otherwise
     */
    private boolean contains(String name) {
    	for (int i = 0; i < this.totalProducts; i++) {
	    if (this.storeProducts[i].getProductName().equals(name)) {
		return true;
	    }
	}
	return false;
    }
	
    /**
     * Prints all the products in this MusicStore.
     */
    public void printProducts(Product[] products) {
	for (int i = 0; i < this.totalProducts; i++) {
	    Product temp = products[i];
	    if (temp == null) continue;
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
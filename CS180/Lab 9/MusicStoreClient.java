import java.util.ArrayList;
import java.util.Scanner;

/**
 * The MusicStoreClient class simulates a MusicStore with interaction from employees, who can add
 * or remove products, and customers who can browse, sort, filter, and purchase products.
 */
public class MusicStoreClient {
    public static void main(String[] args) {
        MusicStore ms = new MusicStore();
        Scanner s = new Scanner(System.in);
        int mainSelection = 0;
	int employeeSelection = 0;
	int customerSelection = 0;
	String productName = "";
	int numSongs = 0;
	double price = 0;
	VideoType type = null;

	System.out.println("Welcome to the Music Store!");
	do {
	    System.out.println("Select an option from the following menu:");
	    System.out.println("1 - Employee: Add or Remove Products to the Store");
	    System.out.println("2 - Customer: Find and Purchase songs from the Store");
	    System.out.println("3 - Exit");
	    mainSelection = s.nextInt();
    
	    if (mainSelection == 1) {
		do {
		    System.out.println("\n---- Employee Menu ----");
		    System.out.println("1 - Add CD");
		    System.out.println("2 - Add DVD");
		    System.out.println("3 - Add MP3");
		    System.out.println("4 - Add MP4");
		    System.out.println("5 - Remove Product");
		    System.out.println("6 - Previous Menu");

		    employeeSelection = s.nextInt();
		    s.nextLine();
		    if (employeeSelection == 1) {
			System.out.println("\nEnter the product name:");
			productName = s.nextLine();
			System.out.println("How many songs are on the CD?");
			numSongs = s.nextInt();
			System.out.println("What is the price of the CD?");
			price = s.nextDouble();
			if (ms.addProduct(new CD(productName, numSongs, price))) {
			    System.out.println("Product added.");
			} else {
			    System.out.println("Product already exists.");
			}
		    } else if (employeeSelection == 2) {
		        System.out.println("\nEnter the product name:");
			productName = s.nextLine();
			System.out.println("Is the DVD a MOVIE or TVSERIES:");
			if (s.nextLine().equalsIgnoreCase("MOVIE")) {
			    type = VideoType.MOVIE;
			} else {
			    type = VideoType.TVSERIES;
			}
			System.out.println("What is the price of the DVD?");
			price = s.nextDouble();
			if (ms.addProduct(new DVD(productName, type, price))) {
			    System.out.println("Product added.");
		        } else {
			    System.out.println("Product already exists.");
		        }
		    } else if (employeeSelection == 3) {
		        System.out.println("\nEnter the product name:");
		        productName = s.nextLine();
		        if (ms.addProduct(new MP3(productName))) {
		            System.out.println("Product added.");
		        } else {
			    System.out.println("Product already exists.");
		        }
		    } else if (employeeSelection == 4) {
		        System.out.println("\nEnter the product name:");
		        productName = s.nextLine();
    		        System.out.println("Is the DVD a MOVIE or TVSERIES:");
		        if (s.nextLine().equalsIgnoreCase("MOVIE")) {
		            type = VideoType.MOVIE;
		        } else {
		            type = VideoType.TVSERIES;
		        }
		        if (ms.addProduct(new MP4(productName, type))) {
			    System.out.println("Product added.");
		        } else {
			    System.out.println("Product already exists.");
		        }
		    } else if (employeeSelection == 5) {
			System.out.println("\nEnter the name of the product to remove:");
			productName = s.nextLine();
			if (ms.removeProductByName(productName)) {
			    System.out.printf("%s removed from the store.%n", productName);
			} else {
			    System.out.printf("%s did not exist in the store.%n", productName);
			}
		    } else if (employeeSelection == 6) {
			System.out.println("\nReturning to the main menu...");
		    } else {
			System.out.println("\nInvalid selection.");
		    }
		} while (employeeSelection != 6);
	    } else if (mainSelection == 2) {
		ArrayList<Product> shoppingCart = new ArrayList<Product>();
		do {
		    System.out.println("\n---- Customer Menu ----");
		    System.out.println("1 - Browse Products");
		    System.out.println("2 - Sort Products by Price (Lowest First)");
		    System.out.println("3 - Sort Products by Price (Highest First)");
		    System.out.println("4 - Filter Products (Audio)");
		    System.out.println("5 - Filter Products (Video)");
		    System.out.println("6 - Filter Products (Downloadable)");
		    System.out.println("7 - Filter Products (Non-Downloadable)");
		    System.out.println("8 - Add Product to Shopping Cart");
		    System.out.println("9 - Checkout");
		    System.out.println("0 - Previous Menu");
		    customerSelection = s.nextInt();
		    if (customerSelection == 1) {
			System.out.println("\n------ Products ------");
			ms.printProducts(ms.getProductsList());
		    } else if (customerSelection == 2) {
			System.out.println("\n------ Products (Filter: Price Ascending) ------");
			ms.printProducts(ms.sortAllProductsByPrice(true));
		    } else if (customerSelection == 3) {
			System.out.println("\n------ Products (Filter: Price Descending) ------");
			ms.printProducts(ms.sortAllProductsByPrice(false));
		    } else if (customerSelection == 4) { 
			System.out.println("\n------ Products (Filter: Audio) ------");
			ms.printProducts(ms.filterAudioOrVideo(true));
		    } else if (customerSelection == 5) {
			System.out.println("\n------ Products (Filter: Video) ------");
			ms.printProducts(ms.filterAudioOrVideo(false));
		    } else if (customerSelection == 6) {
			System.out.println("\n------ Products (Filter: Downloadable) ------");
			ms.printProducts(ms.filterDownloadable(true));
		    } else if (customerSelection == 7) {
			System.out.println("\n------ Products (Filter: Non-Downloadable) ------");
			ms.printProducts(ms.filterDownloadable(false));
		    } else if (customerSelection == 8) {
			System.out.println("\nName of the product to purchase:");
			s.nextLine();
			productName = s.nextLine();
			Product toAdd = ms.getProductByName(productName);
			if (toAdd == null) {
		    	    System.out.println("Product not found.");
			} else {
			    shoppingCart.add(toAdd);
			}
		    } else if (customerSelection == 9) {
			System.out.println("\n----- Shopping Cart -----");
			if (shoppingCart.size() == 0) {
			    System.out.println("Cart is Empty.");
			} else {
			    double total = 0;
			    for (Product item : shoppingCart) {
				System.out.printf("Name:\t%s%n", item.getProductName());
				System.out.printf("Price:\t%.2f%n", item.getPrice());
				if (item instanceof Downloadable) {
			            System.out.printf("Code:\t%s%n", ((Downloadable) item).generateDownloadCode());
				}
				total += item.getPrice();
				System.out.println();
			    }
			    System.out.println("-------------------------");
			    System.out.printf("Total:\t%.2f%n", total);
			}
		    } else if (customerSelection == 0) {
			System.out.println("\nReturning to the main menu...");
		    } else {
			System.out.println("\nInvalid selection.");
		    }
		} while (customerSelection != 0);
	    } else if (mainSelection != 3) {
		System.out.println("\nInvalid selection.");
	    }
	} while (mainSelection != 3);

	System.out.println("\nThanks for visiting the Music Store!");

	s.close();
    }
}
public class Car {
	private int fuel;
	private int distance;
	
	public Car(int fuel) {
		this.fuel = fuel;
		this.distance = 0;
	}
	public void drive(int distance) throws InsufficientFuelException {
		//consumes gas at 20 miles / gallon
		if (distance == 0) {
			this.distance = distance;
			this.fuel = fuel;
		}
		else if (distance < 0) {
			throw new InsufficientFuelException();
		}
		/*if (distance / 20 <= fuel) {
			this.distance = distance;
			this.fuel = fuel - distance / 20;
		}*/
		if (fuel * 20 >= distance) {
			this.distance = distance;
			this.fuel = fuel - distance / 20;
		}
		else {
			throw new InsufficientFuelException();
		}
	}
	
}
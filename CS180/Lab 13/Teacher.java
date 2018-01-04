// Define class Teacher, subclass of AcademicPerson
public class Teacher extends AcademicPerson {
	// Instance variables
	private static final int MAX_COURSES = 10; // maximum courses

	// Constructor
	public Teacher(String name, String address) {
		super(name, address);
		courses = new String[MAX_COURSES];
	}

	
	// It adds a course into the list of courses.
	// This method throws ArrayElementException when the course that is being
	// added to the list already exists in it.
	public void addCourse(String course) throws ArrayElementException {
		for (int i = 0; i < numCourses; i++) {
			if (courses[i] == null) {
				continue;
			}
			if (courses[i].equals(course)) {
				throw new ArrayElementException();
			}
		}
		//if we reach here, the course hasn't been added
		if (numCourses < MAX_COURSES) {
			courses[numCourses] = course;
			numCourses++;
		}
	}

	// It removes a course into the list of courses.
	// This method throws ArrayElementException when the course does not exist
	// in the list.
	public void removeCourse(String course) throws ArrayElementException {
		boolean found = false;
		int index = 0;
		for (int i = 0; i < numCourses; i++) {
			if (courses[i] == null) {
				continue;
			}
			if (courses[i].equals(course)) {
				found = true;
				index = i;
				break;
			}
		}
		if (!found) {
			throw new ArrayElementException();
		}
		else {
			String[] tmp = new String[MAX_COURSES];
			boolean hold = false;
			for (int i = 0; i < numCourses; i++) {
				if (i == index) {
					hold = true;
				}
				if (!hold) {
					tmp[i] = courses[i];
				}
				else {
					tmp[i] = courses[i+1];
				}
			}
			tmp[tmp.length - 1] = null;
			courses = tmp;
		}
	}

	// It prints all the courses in the list in each line
	@Override
	public void printCourses() {
		for (int i = 0; i < numCourses; i++) {
			if (courses[i] == null) continue;
			System.out.println(courses[i]);
		}
	}

	@Override
	public String toString() {
		return "Teacher: " + super.toString();
	}

}
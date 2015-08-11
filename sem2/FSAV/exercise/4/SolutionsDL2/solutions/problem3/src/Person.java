public class Person {

    private int age;

    public void setAge(int newAge) {
	age = newAge;
    }

    public void birthday() {
	if (age >= 29) 
	    throw new ForeverYoungException();
	age++;
    }

}
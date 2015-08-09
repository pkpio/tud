// These classes were just used to illustrate the
// motivation behind JML's visible state semantics.


public class Callback {
	
	/*@ public invariant counter >= 0; @*/ 
	public int counter;
	
	public void  doSomethingUseful(Callback other) {
		counter--;
		
		if (counter > 0) {
			
			other.doSomethingUseful(this);
		
		}
		
		// ...
		
	}
	
	
}


class A1 {

	//@ public invariant c.counter >= 10;
	public Callback c;

}

class A2 {

	public Callback d;
	
	public void m() {
		d.counter = 5;
	}

}
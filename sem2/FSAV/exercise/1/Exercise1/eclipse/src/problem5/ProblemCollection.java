package problem5;

public class ProblemCollection {
	
	
	/*@ public normal_behavior
	  @ requires b > 0;
	  @ ensures \result == a / b;
	  @ assignable \nothing;
	  @*/
	public static int div(int a, int b) {
		return a/b;
	}
	
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures \result == true;
	  @ assignable \nothing;
	  @*/
	public boolean testIdentity(double e) {
		if (e == e) {
			return true;
		}
		return false;
	}
	
	/*@ public normal_behavior
	  @ requires a > 0;
	  @ ensures \result == 42;
	  @ assignable \nothing;
	  @*/
	public static int m(int a) {
		int result = 42;
		if (a > 0) {
		   result = m(a/a);
		}		
		return result;
	}
		
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures \result.val == a;
	  @ assignable \nothing;
	  @*/
	public static MyInteger box(int a) {
		return new MyInteger(a);
	}


	/*@ public normal_behavior
	  @ requires a != b && a!=null && b != null;
	  @ ensures \result.val == a.val * b.val;
	  @ assignable \strictly_nothing;
	  @*/
	public static MyInteger mul(MyInteger a, MyInteger b) {
		return new MyInteger(a.getValue() * b.getValue());
	}

	
	/*@ public invariant 
	  @     (nextCollection != null ==> nextCollection.previousCollection == this) &&
	  @     (previousCollection != null ==> previousCollection.nextCollection == this);
	  @*/
	private /*@ spec_public nullable @*/ ProblemCollection nextCollection;
	private /*@ spec_public nullable @*/ ProblemCollection previousCollection;


	/*@ public normal_behavior
	  @ requires true;
	  @ ensures nextCollection != null;
	  @ assignable nextCollection;
	  @*/
	public void nextAssignment() {
		ProblemCollection nextPC = new ProblemCollection();
		nextCollection = nextPC;
		nextCollection.previousCollection = this;
	}

	/*@ public normal_behavior
	  @ requires true;
	  @ ensures nextCollection != null;
	  @ assignable nextCollection;
	  @*/
	public void nextAssignmentStructured() {
		ProblemCollection nextPC = new ProblemCollection();
		nextCollection = nextPC;
		connectWithNext();
	}
	
	/*@ private normal_behavior
	  @ requires nextCollection != null;
	  @ ensures nextCollection.previousCollection == this;
	  @ assignable nextCollection.previousCollection;
	  @*/
	private void connectWithNext() {
		nextCollection.previousCollection = this;
	}

	
}


final class MyInteger {
	
	private /*@ spec_public @*/ int val;
	
	/*@ public normal_behavior
	  @ ensures this.val == p_val;
	  @ assignable this.val;
	  @*/
	public MyInteger(int p_val) {
		this.val = p_val;
	}
	
	/*@ public normal_behavior
	  @ ensures \result == val;
	  @*/
	public /*@ pure @*/ int getValue() {
		return val;
	}
	
}

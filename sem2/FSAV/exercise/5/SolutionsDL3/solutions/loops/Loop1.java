class Loop1 {

	//@ public invariant x >= 0;
	public int x;


	/*@ public normal_behavior
	  @ requires true;
	  @ ensures \result == x * x;
 	  @ assignable \nothing;
	  @*/
	public int method1() {
		int  y = x;
		int  z = 0;

		/*@ loop_invariant 
		  @     y>=0 && y <= x && z == (x - y) * x;
		  @ decreases y;
		  @ assignable \nothing; 
		  @*/
		while (y > 0) {
			z = z + x;
			y = y - 1;
		}

		return z;
	}
}
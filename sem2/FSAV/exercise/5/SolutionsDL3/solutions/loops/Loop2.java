class Loop2 {

	//@ public invariant x >= 0;
	public int x;
	//@ public invariant y > 0;
	public int y;

	/*@ public normal_behavior
	  @ requires true;
      @ ensures (\exists int q;(\exists int r; 
      @      q >= 0 && r >= 0; \result == q && x == q*y+r)); 
	  @ assignable \nothing;
	  @*/
	public int method2() {    	
		int  x1 = x, q = 0;

		/*@ loop_invariant 
	  	  @     q >= 0 && x == q * y + x1;
	      @ decreases x1;
	      @ assignable \nothing; 
	      @*/
		while (x1 >= y) {
			x1 = x1 - y;
			q = q + 1;
		}

		return q;
	}


}

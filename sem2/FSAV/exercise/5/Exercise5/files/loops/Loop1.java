class Loop1 {

    public int x;

    
    public int method1() {
	int  y = x;
	int  z = 0;
	
	while (y > 0) {
	    z = z + x;
	    y = y - 1;
	}
 
	return z;
    }
}
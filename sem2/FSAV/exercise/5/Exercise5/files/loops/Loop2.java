class Loop2 {
   
    public int x;
    public int y;
    
    public int method2() {
	int  x1 = x, q = 0;

	while (x1 >= y) {
	    x1 = x1 - y;
	    q = q + 1;
	}

	return q;
    }

    
}
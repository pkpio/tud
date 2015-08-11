public class ReverseArray {

    public int[] a;     
   
    public ReverseArray() {
    }
    

 
    public static int[] reverse(int[] p_a) {
        int[] b = new int[p_a.length];
	int i = 0;

	while (i<p_a.length) {      
	    b[i] = p_a[p_a.length-(i+1)];      
	    i++;
	}
	return b;
    }


    
    public void reverseInPlace() {
	// To Be Implemented
    }


    /*@ public normal_behavior
      @ requires true; // COMPLETE
      @ ensures true; // COMPLETE
      @ measured_by 0; // PROVIDE
      @ assignable \nothing;
      @*/
    private static boolean searchHelper(int e, int[] sortedArray, int lo, int hi) {
	if (hi - lo == 0) {
	    return false;
	} else if (hi - lo == 1) {x
	    return sortedArray[lo] == e;
	}

	int mid = lo + (hi - lo) / 2;

	if (sortedArray[mid] > e) {
	    return searchHelper(e, sortedArray, lo, mid); 
	} else {	
	    return searchHelper(e, sortedArray, mid, hi);	    
	}
    }


    /*@ public normal_behavior
      @ requires (\forall int j;
      @     j>=0 && j<sortedArray.length;(\forall int i; i>j && i<sortedArray.length; sortedArray[i] >= sortedArray[j]));
      @ ensures \result == (\exists int i; i>=0 && i<sortedArray.length; sortedArray[i] == e);
      @ assignable \nothing;
      @*/
    public static boolean search(int e, int[] sortedArray) {
	return searchHelper(e, sortedArray, 0, sortedArray.length);
    }

    
}

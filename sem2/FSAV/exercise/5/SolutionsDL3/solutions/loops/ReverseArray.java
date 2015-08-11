public class ReverseArray {

	public int[] a;

	public ReverseArray() {
	}

	/*@ public normal_behavior
      @ requires p_a.length>=0;
      @ ensures (\forall int j; j>=0 && j<p_a.length; \result[j]==p_a[p_a.length-(j+1)]) &&
      @   \result.length == p_a.length;
      @ assignable \nothing;
      @*/
	public static int[] reverse(int[] p_a) {
		int[] b = new int[p_a.length];
		int i = 0;
		/*@ loop_invariant (\forall int j; j>=0 && j<i; b[j]==p_a[p_a.length-(j+1)]) && i>=0 && i<=p_a.length;
          @ assignable b[*];
          @ decreases p_a.length - i;
          @*/
		while (i < p_a.length) {
			b[i] = p_a[p_a.length - (i + 1)];
			i++;
		}
		return b;
	}

	/*@ public normal_behavior
      @ ensures (\forall int j; j>=0 && j<\old(a.length); a[j]==\old(a[a.length-(j+1)]));
      @ assignable a[*];
      @*/
	public void reverseInPlace() {
		int i = 0;
		/*@ loop_invariant (\forall int j; j>=0 && j<i; a[j]==\old(a[a.length-(j+1)]) && 
	  	  @                            \old(a[j])==a[a.length-(j+1)]) 
	      @                && (\forall int j; j>=i && j<=a.length-(i+1); \old(a[j]) == a[j])
	      @                && i>=0 && i<=a.length/2;
          @ assignable a[*];
	      @ decreases a.length - i;
          @*/
		while (i < a.length / 2) {
			int tmp = a[i];
			a[i] = a[a.length - (i + 1)];
			a[a.length - (i + 1)] = tmp;
			i++;
		}
	}

	/*@ public normal_behavior
      @ requires (\forall int i;
      @    (\forall int j; j>=0 && j<i && i<sortedArray.length; sortedArray[i] >= sortedArray[j])) &&
      @    lo>=0 && lo <= hi && hi<=sortedArray.length;
      @ ensures \result == (\exists int i; i>=lo && i<hi; sortedArray[i] == e);
      @ measured_by hi - lo;
      @ assignable \nothing;
      @*/
	private static boolean searchHelper(int e, int[] sortedArray, int lo, int hi) {
		if (hi - lo == 0) {
			return false;
		} else if (hi - lo == 1) {
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
      @     j>=0 && j<sortedArray.length;
      @        (\forall int i; i>j && i<sortedArray.length; sortedArray[i] >= sortedArray[j]));
      @ ensures \result == (\exists int i; i>=0 && i<sortedArray.length; sortedArray[i] == e);
      @ assignable \nothing;
      @*/
	public static boolean search(int e, int[] sortedArray) {
		return searchHelper(e, sortedArray, 0, sortedArray.length);
	}

}

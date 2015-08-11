public class Coll {

    public static boolean contains(int e, int[] a) {
		boolean found = false;
		int i = 0;
		/*@ loop_invariant 
		  @   i>=0 && i<=a.length && 
		  @      (found == false <==> 
		  @         (\forall int j; j>=0 && j<i; a[j] != e));
		  @ assignable i, found;
		  @ decreases a.length - i;
		  @*/
		while (i < a.length) {
			if (a[i] == e) {
				found = true;
			}
			i++;
		}
		return found;
    }
	
}
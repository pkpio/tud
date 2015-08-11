public class CollClient {

    /*@ public normal_behavior 
      @ ensures \result == (\exists int i; i>=0 && i<a.length;a[i] == 0);
      @ assignable \nothing;
      @*/
    public static boolean containsZero(int[] a) {
		return Coll.contains(0, a);
    }

}
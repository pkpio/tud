package verify;

public class ArrayHelper {

    /*@ public normal_behavior	
      @ requires newE > array[at] && at >= 0 && at < array.length;
      @ ensures array[at] == newE;
      @ assignable array[at];
      @
      @ also
      @
      @ public normal_behavior
      @ requires newE <= array[at] && at >= 0 && at < array.length;
      @ ensures true;
      @ assignable \nothing;
      @*/
    public static void replaceIfGreater(int newE, int at, int[] array) {
		if (newE > array[at]) {
			array[at] = newE;
		}
    }
    
 }
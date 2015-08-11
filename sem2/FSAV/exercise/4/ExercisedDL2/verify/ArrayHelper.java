public class ArrayHelper {

    /*@ public normal_behavior
      @ requires newE > array[at];
      @ ensures array[at] == newE;
      @
      @ also
      @
      @ public normal_behavior
      @ requires newE <= array[at];
      @ ensures true;
      @ assignable \nothing;
      @*/
    public static void replaceIfGreater(int newE, int at, int[] array) {
		if (newE > array[at]) {
			array[at] = newE;
		}
    }


}
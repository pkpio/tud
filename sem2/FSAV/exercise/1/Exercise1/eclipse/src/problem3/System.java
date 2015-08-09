package problem3;

public class System {

	/*@ public normal_behavior
	  @ requires srcPos >= 0 && destPos >= 0 && length >= 0 && (destPos + length) < dest.length
	  @ && (srcPos + length) < src.length;
	  @ ensures src[srcPos] == dest[destPos];
	  @*/
	public static void arraycopy(int[] src, int srcPos, int[] dest,
			int destPos, int length) {
		// here should be an implementation
		src[srcPos] = dest[destPos];
	}

}

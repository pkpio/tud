public class MathHelper {

    /**
     * computes the absolute difference of <tt>a</tt> and <tt>b</tt>
     *
     * @returns <tt> | a - b | </tt> 
     */
    public static int absDiff (int a, int b) {
	if ( a < b ) {
	    a = a - b;
	    b = a + b;
	    a = b - a;
        }

	return a - b;
    }

    /**
     * returns the maximum of both parameters
     */
    public static int max(int a, int b) {
	return a < b ? b : a;
    }

}
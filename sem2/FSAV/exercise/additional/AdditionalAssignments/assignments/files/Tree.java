package snippet;

public final class Tree {

    private /*@ spec_public @*/ int value;
    private /*@ spec_public @*/ Tree left;
    private /*@ spec_public @*/ Tree right;

    /*@ public invariant 
      @
      @
    */

    public int /*@ strictly_pure @*/ max () {
        int res = value;
        if (left != null) {
            res = maxHelper(res,left.max(),right.max());
        }
        return res;
    }

    /*@ public normal_behavior
      @ ensures \result >= x;
      @ ensures \result >= y;
      @ ensures \result >= z;
      @ ensures \result == x || \result == y || \result == z;
      @ 
      @*/
    public int /*@ strictly_pure helper @*/ maxHelper(int x, int y, int z) {
        if (x > y) return (x > z? x: z);
        else return (y > z? y: z);
    }
}

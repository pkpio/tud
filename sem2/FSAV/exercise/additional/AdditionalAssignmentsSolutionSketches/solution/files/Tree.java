package snippet;

public final class Tree {

    private /*@ spec_public @*/ int value;
    private /*@ nullable spec_public @*/ Tree left;
    private /*@ nullable spec_public @*/ Tree right;

    /*@ public invariant left == null <==> right == null;
      @ public invariant left != null ==> 
      @                   (\invariant_for(left) && \invariant_for(right));
      @*/

    
    // the invariant below only guarantees acyclicity in conjunction with both upper invariants;
    // why? Also, additional exercise: try to formalize acyclity in a more direct way using \reach.
    /*@ public invariant (\exists int n; n>=0 && (\forall Tree t; !\reach(this.left, this, t, n) && 
      @    !\reach(this.right, this, t, n)));
      @*/ 
        
    //@ accessible \inv: \reachLocs(left,this), \reachLocs(right,this);
    
    /*@ public model int height;
      @ represents height \such_that height >= 0 &&
      @ (left != null ==>
      @                   (height > left.height && height > right.height));
      @*/

    /*@ public model \seq values;
      @ represents values \such_that values == \seq_concat(\seq_singleton(value),
      @           (left == null) ? \seq_empty
      @                       : \seq_concat(left.values,right.values));
      @*/

    /*@ public normal_behavior
      @ ensures (\forall int z; 
      @     (\exists int i; i>=0 && i<values.length && this.values[i] == z); 
      @                     z <= \result);
      @ ensures (\exists int i; i>=0 && i<this.values.length; this.values[i] == \result);
      @ measured_by height;
      @*/
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

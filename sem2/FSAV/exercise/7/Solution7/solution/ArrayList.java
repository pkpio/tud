public final class ArrayList implements List {

    private int[] a = new int[0];
    /*@ private represents theList =
      @     (\seq_def int i; 0; a.length; a[i]);
      @*/

    //@ private represents footprint = \set_union(\singleton(a), a[*]);
        
    
    public void add (int elem) {
        int[] tmp = new int[a.length+1];
        /*@ loop_invariant 0 <= i && i <= a.length;
          @ loop_invariant (\forall int j; i < j && j <= a.length; 
          @                 tmp[j] == \old(a[j-1]));
          @ decreasing i;
          @ assignable tmp[*];
          @*/
        for (int i= a.length; i > 0; i--)
            tmp[i] = a[i-1];
        a = tmp;
        a[0] = elem;
    }

    public void remFirst () {
        int[] tmp = new int[a.length-1];
        /*@ loop_invariant 0 < i && i <= a.length;
          @ loop_invariant (\forall int j; 0 < j && j < i; 
          @                 tmp[j-1] == \old(a[j]));
          @ decreasing a.length - i;
          @ assignable tmp[*];
          @*/
        for (int i= 1; i < a.length; i++)
            tmp[i-1] = a[i];
        a = tmp;
    }

    public boolean empty () {
        return size() == 0;
    }

    public int size () {
        return a.length;
    }

    public int get (int idx) {
        return a[idx];
    }
}

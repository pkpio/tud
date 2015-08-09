package snippet;

public class Snippet {
    
    /*@ public normal_behavior
      @  requires true;
      @  ensures \result == (\sum int i; 0 <= i && i < a.length; \old(a[i])) &&
      @     (\forall int i; i>=0 && i<a.length; a[i] == 0);
      @  assignable a[*];
      @*/
    public static int sum(int[] a)
    {
        int s = 0, n=0;
        while(n < a.length)
        {
            s += a[n];
            a[n] = 0;
            n++;
        }
        return s;
    }
    
}


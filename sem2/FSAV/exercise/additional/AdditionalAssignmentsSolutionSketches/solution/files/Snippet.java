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
    /*@ loop_invariant n>=0 && n<=a.length && 
      @     s == (\sum int i; 0 <= i && i < n; \old(a[i])) &&
      @     (\forall int i; i>=n && i<a.length; a[i] == \old(a[i])) &&
      @     (\forall int i; i>=0 && i<n; a[i] == 0);
      @ assignable a[*]; //s, n are automatically added 
      @ decreasing a.length - n;
      @*/
    while(n < a.length)
    {
        s += a[n];
        a[n] = 0;
        n++;
    }
    return s;
    }
    
}


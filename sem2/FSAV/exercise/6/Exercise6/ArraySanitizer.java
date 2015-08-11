class ArraySanitizer {

    static int[] removeDup(int[] a) {
        int[] result = new int[a.length];
        int p = 0;

        for(int k = 0; k < a.length; k++) {
            if(!contains(result, p, a[k])) {
                result[p] = a[k];
                p++;
            }
        }
        return arrayPart(result, p);
    }

    /*@ public normal_behavior
      @   requires 0<=len && len <= a.length;
      @   ensures \result <==> (\exists int i; 0<=i && i<len; a[i] == v);
      @   assignable \strictly_nothing;
      @*/
    static boolean contains(int a[], int len, int v) {
        for(int i = 0; i < len; i++) {
            if(a[i] == v) {
                return true;
            }
        }
        return false;
    }


    /*@ public normal_behavior
      @   requires 0 <= length && length <= a.length;
      @   ensures \result.length == length;
      @   ensures \fresh(\result);
      @   ensures (\forall int i; 0<=i && i < length; \result[i] == a[i]);
      @   assignable \nothing;
      @*/
    static int[] arrayPart(int[] a, int length) {
        int[] result = new int[length];

        for(int i = 0; i < length; i++) {
            result[i] = a[i];
        }
        return result;
    }
}


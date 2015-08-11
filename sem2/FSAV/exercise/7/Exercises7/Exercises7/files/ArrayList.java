public final class ArrayList implements List {

    private int[] a = new int[0];

    public void add (int elem) {
        int[] tmp = new int[a.length+1];
        for (int i= a.length; i > 0; i--)
            tmp[i] = a[i-1];
        a = tmp;
        a[0] = elem;
    }

    public void remFirst () {
        int[] tmp = new int[a.length-1];
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

public interface List {

    public void add (int elem);

    /**
     * removes the first element from the list
     */
    public void remFirst ();

    /**
     * returns true iff the list is empty
     */
    public boolean empty ();

    /**
     * returns the size of the list
     */
    public int size ();

    /**
     * returns the  idx-th element of the list
     */
    public int get (int idx);
}

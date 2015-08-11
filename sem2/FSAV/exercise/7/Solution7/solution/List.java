public interface List {
    //@ public instance model \seq theList;
    //@ public instance model \locset footprint;
    //@ accessible footprint: footprint;
    
    
    /*@ public normal_behavior
      @ ensures theList == \seq_concat(\seq_singleton(elem),
      @                                \old(theList));
      @ assignable footprint;
      @*/
    public void add (int elem);

    /*@ public normal_behavior
      @ requires !empty();
      @ ensures theList == \old(theList[1..theList.length]);
      @ assignable footprint;
      @*/
    public void remFirst ();

    /*@ public normal_behavior
      @ ensures \result == (size() == 0);
      @ accessible footprint;
      @*/
    public /*@ pure @*/ boolean empty ();

    /*@ public normal_behavior
      @ ensures \result == theList.length;
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int size ();

    /*@ public normal_behavior
      @ requires 0 <= idx && idx < size();
      @ ensures \result == (int)theList[idx];
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int get (int idx);
}

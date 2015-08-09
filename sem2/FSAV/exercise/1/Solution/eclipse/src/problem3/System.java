package problem3;

public class System {

	// How many specification cases depends on the chosen granularity?
	// A suggestion would be 8:
	//    1 spec. case for NullPointerException (dest or src is null)
	//    1 spec. case for ArrayIndexOutOfBoundException
	//    2 spec. cases for ArrayStoreExceptions:
	//           1: for the cases where the type error leading to the exception can be deduced by the runtime type of the passed src and dest
	//           1: for the case where the type error is first found when trying to copy an incompatible element 
	//    1 for the successfull method invocation (normal) behavior  [[ 2 are also possible when you 
	//                                               want to distinguish both cases same or different array objects as src and dest]]
	
	
	

	// on the specification level we access src  in the prestate, hence, the case distinction for src==dest is not needed 
	/*@ public normal_behavior
	  @ ensures (\forall int i; i>=0 && i<length; dest[destPos + i] == \old(src[srcPos+i]));
	  @ assignable dest[destPos..destPos+length];
	  @*/
	public static void arraycopy(int[] src, int srcPos, int[] dest, int destPos, int length) {
		// here should be an implementation
	}
	
}

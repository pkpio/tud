// This interface was only used to develop a quantified expression interactively
// For other examples, see the slides. 
public interface QuantifiedExpressions {

	
	
	/*@ public normal_behavior
	  @ requires a.length > 0;
	  @ ensures (\exists int i; 0<= i && i<a.length; (\forall int j;
	  @       0<=j && j<a.length && i != j; a[i] >= a[j] && \result == a[i]
	  @ ) ); 
	  @*/
	public int getMax(int[] a);
		
}

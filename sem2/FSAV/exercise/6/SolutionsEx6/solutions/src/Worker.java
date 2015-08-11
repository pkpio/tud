public class Worker {
   //@ private ghost int successfulTries;
   //@ private ghost int unsuccessfulTries;
	
   /*@ public normal_behavior
	 @ ensures true;
	 @ assignable \nothing;
	 @*/
   public boolean doTry() {
	   throw new RuntimeException("To be implemented in subclasses.");	   
   }

   /*@ public normal_behavior
     @ ensures \result ==> successfulTries == \old(successfulTries) + 1 &&
     @                     unsuccessfulTries >= \old(unsuccessfulTries) &&
     @                     unsuccessfulTries <= \old(unsuccessfulTries) + 2;
     @ ensures !\result ==> successfulTries == \old(successfulTries) &&
     @                      unsuccessfulTries == \old(unsuccessfulTries) + 3;
     @*/
   public boolean tryMaximalThreeTimes() {
      int i = 0;
      boolean done = false;
      /*@ loop_invariant i>=0 && i<=3
        @ && unsuccessfulTries >= \old(unsuccessfulTries)  
        @ && successfulTries + unsuccessfulTries - i == \old(successfulTries + unsuccessfulTries) 
      	@ && (done ? successfulTries - \old(successfulTries) == 1 : successfulTries == \old(successfulTries));  
      	@ assignable this.successfulTries, this.unsuccessfulTries;
      	@ decreases 3 - i;
      	@*/
      while (i < 3 && !done) {
         if (doTry()) {
            //@ set successfulTries = successfulTries + 1;
            done = true;
         }
         else {
            //@ set unsuccessfulTries = unsuccessfulTries + 1;
            done = false;
         }
         i++;
      }
      return done;
   }
}
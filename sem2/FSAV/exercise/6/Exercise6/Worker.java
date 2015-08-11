public class Worker {
	
   /*@ public normal_behavior
     @ ensures true;
     @ assignable \nothing;
     @*/
   public boolean doTry() {
       // imagine some implementation here and ignore the actual code
       // the following line is just so that the class compiles
       // for specification and verification of tryMaximalThreeTimes you
       // have only the knowledge of the above given contract
       throw new RuntimeException("Not implemented here"); // this line is just for compilation reasons
   }

   public boolean tryMaximalThreeTimes() {
      int i = 0;
      boolean done = false;
      while (i < 3 && !done) {
         if (doTry()) {
            done = true;
         }
         else {
            done = false;
         }
         i++;
      }
      return done;
   }
}

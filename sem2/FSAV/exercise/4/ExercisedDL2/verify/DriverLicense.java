public class DriverLicense {

    private long counter = 0;

    private /*@ spec_public @*/ boolean active;

    /*@ public invariant (\forall DriverLicense l; l.licenseNr == this.licenseNr; l == this); @*/
    private /*@ spec_public @*/ int licenseNr;

    public DriverLicense() {
	this.active = false;
	this.licenseNr = counter;
	counter++;
	if (counter < 0) {
	    throw new RuntimeException("No more licenses available.");
	}
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == licenseNr;
      @*/
    public /*@ pure @*/ int licenseNr() {
	return licenseNr;
    }

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == active;
      @*/
    public /*@ pure @*/ boolean active() {
	return active;
    }

    /*@ public normal_behavior
      @ requires true;
      @ ensures this.active == p_active;
      @ assignable active;
      @*/
    public void setActive(boolean p_active) {
	this.active = p_active;
    } 

}
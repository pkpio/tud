package stepcounter;
/**
 * General interface to be implemented by a step counter
 * A step counter counts the number of steps until a  
 * {@ link #reset()} occurs. After resetting the counting 
 * starts again with 0 steps. 
 * The hardware informs the counter regularly about the detected steps
 * using method {@link #incSteps(int)}.
 */
public interface StepCounter {
	
	//@ public instance invariant getStepsTotal() >= 0;
	//@ public instance invariant getStepSize() >= 0;
	//@ public instance invariant getStepSize() * getStepsTotal() == getDistance();
	
	
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures getStepsTotal() == 0;
	  @*/
	public void reset();

	/*@ public normal_behavior
	  @ requires p_inc >= 0;
	  @ ensures getStepsTotal() == \old(getStepsTotal()) + p_inc;
	  @*/
	public void incSteps(int p_inc);

	public /*@ pure @*/ int getStepsTotal();

	public /*@ pure @*/ int getStepSize();
	
	public /*@ pure @*/ int getDistance();
	
	/*@ public normal_behavior
	  @ requires size >= 0;
	  @ ensures getStepSize() == size;
	  @*/
	public void setStepSize(int size);
}


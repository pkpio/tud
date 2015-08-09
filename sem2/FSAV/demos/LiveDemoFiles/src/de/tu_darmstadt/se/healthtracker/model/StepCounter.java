package de.tu_darmstadt.se.healthtracker.model;

/**
 * General interface to be implemented by a step counter. A step counter tracks
 * the number of steps until a {@link reset()} occurs. After resetting, counting
 * restarts with 0 steps. Call {@link incSteps(int)} to update counter. Walked
 * distance is computed using the total number of steps and the step size.
 */
public interface StepCounter {

	//@ public instance invariant getStepsTotal() >= 0;
	//@ public instance invariant getStepSize() >=0;

	public /*@ pure @*/ int getStepsTotal();

	/*@ public normal_behavior
	  @ ensures getStepsTotal() == 0;
	  @*/
	public void reset();

    /*@ public normal_behavior
      @ requires getStepsTotal() >= 0;
      @ ensures getStepsTotal() == \old(getStepsTotal()) + p_inc;
      @ ensures getStepsTotal() >= 0;
      @*/
	public void incSteps(int p_inc);

	public int getStepSize();

	public int getDistance();

	public void setStepSize(int size);
}

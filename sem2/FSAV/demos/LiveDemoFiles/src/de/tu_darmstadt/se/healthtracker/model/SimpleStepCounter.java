package de.tu_darmstadt.se.healthtracker.model;

public class SimpleStepCounter extends Category implements StepCounter {

	//@private invariant stepSize >= 0;
	
	/* The JML expression below expresses the same statement, but as a static invariant.
	   private static invariant 
	    (\forall SimpleStepCounter o; o.stepSize >= 0);
	 */
	
	private int stepsTotal;
	private int stepSize;

	public SimpleStepCounter(int p_stepsTotal, int p_stepSize) {
		this.stepsTotal = p_stepsTotal;
		this.stepSize = p_stepSize;
	}

	public void incSteps(int p_inc) {
		this.stepsTotal += p_inc;
	}

	public int getStepsTotal() {
		return stepsTotal;
	}

	public int getStepSize() {
		return stepSize;
	}

	@Override
	public int getDistance() {
		return stepsTotal * stepSize;
	}

	public void reset() {
		stepsTotal = 0;
		stepSize = 0;
	}

	public void setStepSize(int p_size) {
		this.stepSize = p_size;
	}

	
	public void mergeCounters(StepCounter p_other) {

		int otherSteps = p_other.getStepsTotal();

		int ownSteps = this.getStepsTotal();

		this.stepsTotal = otherSteps + ownSteps;

	}

}

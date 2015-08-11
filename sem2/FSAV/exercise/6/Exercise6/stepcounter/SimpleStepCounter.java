package stepcounter;
public class SimpleStepCounter implements StepCounter {

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
	
}

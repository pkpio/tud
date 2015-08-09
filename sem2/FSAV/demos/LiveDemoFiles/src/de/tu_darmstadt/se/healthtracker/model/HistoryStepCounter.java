package de.tu_darmstadt.se.healthtracker.model;

public class HistoryStepCounter extends Category implements StepCounter {
	
	/** sum of all steps in the tracked time period */	
	private int stepsTotal;	

	/** records steps per day */ 
	private int[] history;
	
	/** day counter */
	private int now;

	/** size of a step in centimeters */
	private /*@ spec_public @*/ int stepSize;
	
	public HistoryStepCounter(int p_goalPerDay, int p_maxLenHistory) {
		this.history = new int[p_maxLenHistory];
		this.stepsTotal = 0;	
		this.now = 0;
	}
	
	public void reset() {
		this.stepsTotal = 0;
		this.history = new int[history.length];
		this.now = 0;
	}
	
	public void incSteps(int p_inc) {
		history[now] += p_inc; 
		this.stepsTotal += p_inc;
	}
	
	public void nextDay() {
		if (now >= history.length - 1) {
			throw new IndexOutOfBoundsException("Maximum history entries reached.");
		} else { 
 			now++;
			history[now] = 0;
		}		
	}

	public int now() {
		return now;
	}
	
	public int getStepsTotal() {
		return stepsTotal;
	}
	
	public int getStepsAtDay(int p_day) {
		return history[p_day];
	}

	public int getStepSize() {
		return stepSize;
	}

	
	public int getDistance() {
		return stepSize * stepsTotal;
	}

	/*@ public normal_behavior
	  @ requires p_size >= 0;
	  @ ensures getStepSize() == p_size;
	  @ assignable stepSize;
	  @*/
	public void setStepSize(int p_size) {
		this.stepSize = p_size;
	}
	
}

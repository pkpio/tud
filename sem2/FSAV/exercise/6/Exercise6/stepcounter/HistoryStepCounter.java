package stepcounter;
public class HistoryStepCounter implements StepCounter {
	
	/** records steps per day */ 
	private /*@ spec_public @*/ int[] history;
	
	/** day counter */
	//@ public invariant now >= 0; 
	private /*@ spec_public @*/ int now;

	/** size of a step in centimeters */
	private int stepSize;
	
	public HistoryStepCounter(int p_goalPerDay, int p_maxLenHistory) {
		this.history          = new int[p_maxLenHistory];
		this.now 			  = 0;
	}
    
    // Implementation of interface
	
	public void reset() {
		this.history		  = new int[history.length];
		this.now 		      = 0;
	}
	
	public void incSteps(int p_inc) {
		history[now] += p_inc; 
	}
	
	public int getStepsTotal() {
        int accumulatedSteps = 0;
        for (int i = 0; i<=now; i++) {
            accumulatedSteps += history[i];
        }
		return accumulatedSteps;
	}
	
	public int getStepSize() {
		return stepSize;
	}

	public int getDistance() {
		return stepSize * getStepsTotal();
	}

	public void setStepSize(int p_size) {
		this.stepSize = p_size;
	}

    // Class specific methods
    
    /*@ public normal_behavior
     @ requires p_day >= 0 && p_day < history.length;
     @*/
    public /*@ pure @*/ int getStepsAtDay(int p_day) {
        return history[p_day];
    }

    /*@ public normal_behavior
     @ requires now < history.length - 1;
     @ ensures now == \old(now) + 1;
     @ ensures history[now] == 0;
     @ assignable now, history[now];
     @*/
    public void nextDay() {
        if (now >= history.length - 1) {
            throw new IndexOutOfBoundsException("Maximum history entries reached.");
        } else {
            now++;
            history[now] = 0;
        }
    }
    
    /*@ public normal_behavior
      @ ensures \result == now;
      @*/
    public /*@ pure @*/ int now() {
        return now;
    }

}

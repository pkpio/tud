/**
 * Only partial solution:
 *   represents clauses for model fields are declared and at some methods
 *   additional specifications are added as needed. Other specs inherited
 *   from super classes. 
 *   
 *   For a complete specification it is needed to check if additional specs 
 *   are needed like loop invariants (for some loops and/or methods)
 */
package stepcounter;

public class HistoryStepCounter implements StepCounter {
	
	/** records steps per day */ 
	//@ represents _stepsTotal = (\sum int i; 0<=i && i<=now; history[i]);
    private /*@ spec_public @*/ int[] history;
    
	
	/** day counter */
	//@ public invariant now >= 0; 
	private /*@ spec_public @*/ int now;

	/** size of a step in centimeters */
    //@ represents _stepSize = stepSize;
	private int stepSize;
	
	public HistoryStepCounter(int p_goalPerDay, int p_maxLenHistory) {
		this.history          = new int[p_maxLenHistory];
		this.now 			  = 0;
	}
    
    // Implementation of interface
	
    /*@ also
      @ public normal_behavior
      @ ensures now == 0;
      @ assignable now, history;
      @*/
    public void reset() {
		this.history		  = new int[history.length];
		this.now 		      = 0;
	}
	
    /*@ also
      @ public normal_behavior
      @ ensures history[now] == \old(history[now]) + p_inc;
      @ assignable now, history;
      @*/
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

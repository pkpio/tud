package de.tu_darmstadt.se.healthtracker.model;

import de.tu_darmstadt.se.healthtracker.model.Category;

public class HealthTracker {

	private /*@ spec_public @*/ String username;

	
	//@ invariant \typeof(category) == \type(Category[]);
	private /*@ spec_public @*/ Category[] category;	
	
	private /*@ spec_public @*/ int nrCategories;

	/*@ public normal_behavior
	  @ requires p_category != null && category != null && nrCategories >= 0;
	  @ requires nrCategories >= category.length - 1; 
	  @ ensures \result == false;
	  @ 
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires p_category != null && category != null && nrCategories >= 0;
	  @ requires nrCategories < category.length - 1; 
	  @ requires (\exists int i; i>=0 && i<nrCategories; p_category.id == category[i].id);
	  @ ensures \result == false;
	  @ 
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires p_category != null && category != null && nrCategories >= 0; 
	  @ requires nrCategories < category.length - 1;
	  @ requires (\forall int i; i>=0 && i<nrCategories; p_category.id != category[i].id);
	  @ ensures category[nrCategories - 1] == p_category;
	  @ ensures nrCategories == \old(nrCategories + 1);
	  @ ensures \result;
	  @ assignable nrCategories, category[nrCategories];
	  @*/
	public boolean addCategory(Category p_category) {
		int id = p_category.getId();
		
		if (nrCategories >= category.length - 1) {
			return false;
		} else if (findCategoryById(id) != null) {
			return false;
		} 
		
		category[nrCategories] = p_category;
		nrCategories++;
		
		return true;
	}
	
	/*@ public normal_behavior
	  @ requires (\exists int i; i >= 0 && i<nrCategories; category[i].id == p_id);
	  @ requires category != null && nrCategories >= 0  && nrCategories <= category.length;
	  @ ensures \result != null && \result.id == p_id;
	  @ 
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires !(\exists int i; i >= 0 && i<nrCategories; category[i].id == p_id);
	  @ requires category != null && nrCategories >= 0  && nrCategories <= category.length;
	  @ ensures \result == null;
	  @*/
	public /*@ nullable pure @*/ Category findCategoryById(int p_id) {
		/*@ loop_invariant 
		  @ 	(\forall int j; j>=0 && j<i; category[j].id != p_id)
		  @ 	&& i >= 0 && i<=nrCategories;
		  @ decreases nrCategories - i;
		  @ assignable \nothing;
		  @*/
		for (int i = 0; i < nrCategories; i++) {
			if (p_id == category[i].getId()) {
				return category[i];
			}
		}	
		return null;
	}
		
	public HealthTracker(String username, int maximalNumberOfCategories) {
		this.username = username;
		this.category = new Category[maximalNumberOfCategories];
		this.nrCategories = 0;
	}
	
	/**
	 * returns the number of categories managed by the tracker 
	 * @return the managed number of categories
	 */
	public int getNumberCategories() {
		return nrCategories;
	}
	
	/**
	 * returns the maximal number of categories this tracker can manage
	 */
	public int getMaxNumberCategories() {
		return category.length;
	}
	
	/**
	 * retrieves the name of the tracked user
	 * @return the name of the user
	 */
	public String getUsername() {
		return username;
	}

	/**
	 * removes the specified category and returns true if the removal was successful, i.e.,
	 * the category was found
	 * @param p_category the {@link Category} to remove
	 * @return true if the category was removed
	 */
	public boolean removeCategory(Category p_category) {		
		/* for (int i = 0; i < nrCategories; i++) {
			if (category[i] == p_category) {
				System.arraycopy(category, i+1, category, i, nrCategories - (i + 1));				
				nrCategories--;
				return true;
			}
		} */
		return false;
	}
}

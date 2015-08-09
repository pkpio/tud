package de.tu_darmstadt.se.healthtracker.model;

public class Category {
	
	private /*@ spec_public @*/ int id;
	 
	/*@ public normal_behavior
	  @ ensures \result == this.id;
	  @*/
	public /*@ pure helper @*/ int getId() {
		return id;
	}
	
}

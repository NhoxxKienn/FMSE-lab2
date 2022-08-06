/*
 * Lab Gruppe 128
 * Mitglied:
 * Van Duc Hoang
 * Duc Bach Lai
 * Minh Huy Tran: mt45qyry
 * Zhijingshui Yang: zy53zahy
*/

public class proof_analysis {
	
	/*@ public invariant next.previous == this && previous.next == this; */
	private /*@ spec_public @*/ proof_analysis next;
	private /*@ spec_public @*/ proof_analysis previous;
	
    /*@ public invariant 0 <= lookup && lookup < values.length; */
    private /*@ spec_public @*/ int[] values;
    private /*@ spec_public @*/ int lookup;
    
    
    /*@ public normal_behaviour
      @ assignable previous, predecessor.next;
      @ ensures previous == predecessor && predecessor.next == this;
      @*/
    public void changePrev(proof_analysis predecessor) {
    	previous = predecessor;
    	predecessor.next = this;
    }
    
    
    /*@ public normal_behaviour
      @ requires 0 <= index && index < values.length;
      @ assignable values[index];
      @ ensures values[index] == element;
      @*/
    public boolean set(int element, int index) {
    	if (index < 0 || index >= values.length) return false;
    	values[index] = element;
    	return true;
    }
    
    /*@ public normal_behaviour
      @ requires 0 <= i && 0 <= j && i < values.length && j < values.length;
      @ assignable values[i], values[j];
      @ ensures values.length == \old(values.length);
      @ ensures values[i] == \old(values[j]) && values[j] == \old(values[i]);
      @ ensures \result;
      @*/
    public boolean swapValues(int i, int j) {
    	if (i < 0 || j < 0 || i >= values.length || j >= values.length) throw new ArrayIndexOutOfBoundsException();
    	int a = values[i];
    	int b = values[j];
    	return set(a, j) && set(b, i); 
    }
    
    
    /*@ public normal_behavior
      @ assignable values[*], lookup;
      @ ensures \old(values[lookup]) == values[lookup];
      @ ensures \old(values[lookup]) != \old(values)[\old(lookup)];
      @*/
    public void action() {
       values[lookup - 1] = values[lookup];
       values[lookup] = values[lookup] + 1;
       lookup--;
    }
    
    
    
    
    
    /* ----------------------------------FRAGEBOGEN-----------------------------------
     * 
     * -------------------------------------------------------------------------------
     * Frage 1: Warum erf�llt die Methode changePrev(predecessor) ihre Spezifikation nicht? 
     * -------------------------------------------------------------------------------
     * Antwort 1: [...]
     * Falls predecessor != this && this.next = this, dann ist this.prev = predecessor 
     * aber this.next bleibt unverändert this.next = this => next.prev = this.prev = predecessor
     * Aber das Invariant regelt sich, dass this.next.prev = this
     * => Widerspruch
     * -------------------------------------------------------------------------------
     * Frage 2: Versuchen Sie die Methode swapValues(int i, int j) unter Method 
     *    Treatment 'Contract' und 'Expansion' zu verifizieren. Unter welchem
     *    Treatment kann KeY den Beweis schlie�en? Falls KeY den Beweis nicht
     *    schlie�en kann, warum?
     * -------------------------------------------------------------------------------
     * Antwort 2: [...]
     * Method Treatment 'Contract' verifiziert sich nicht, 
     * da im Contract von normal_behaviour von set wird es nicht sicher gestellt, dass die Methode true zurueckliefern wird.
     * Deshalb nehme es noch an, dass set kann false sein und gibt an einen Widerspruch mit ensures \result
     * 
     * Method Treatment 'Expand' kann es verifizieren. 
     * Da es den ganzen Koerper von set darin einsetzt, deshalb liefert das am Ende immer true zurueck.
     * -------------------------------------------------------------------------------
     * Frage 3: Warum erf�llt die Methode action() ihre Spezifikation nicht?
     * -------------------------------------------------------------------------------
     * Antwort 3: [...]
     * Falls lookup =  0, nach ende der Methode wird lookup = -1 
     * => Widerspruch mit dem Invariant
     */
    
    
    
    /*@ public normal_behavior
      @ ensures \old(values[lookup]) == values[lookup];
      @ ensures 2 * \old(values[lookup]) == \old(values)[\old(lookup)] - lookup;
      @ assignable lookup, values[-values[lookup]];
      @*/
    public void action2() {
        values[-values[lookup]] = values[lookup];
        lookup = -values[lookup];
    }
    
}


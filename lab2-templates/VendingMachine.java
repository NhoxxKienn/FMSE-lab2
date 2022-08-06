public class VendingMachine {
	
	/*
	 * A vending machine has N item slots.
	 */
	private /*@spec_public */ final int N = 3;
	
	/*
	 * The name of an item in a slot is given by the String in the same index in this array, e.g. slot 0 stores Water.
	 */
	private /*@spec_public */ final String[] itemNames = new String[] {"Water", "Lemonade", "Chocolate"};
	
	/*
	 * This array stores for each item slot the quantity of items in that slot. 
	 */
	private /*@spec_public */ int[] items = new int[N];
	/*@ public invariant (\forall int i; i >= 0 && i < N; items[i] != null && items[i] >= 0); @*/
	/*@	public invariant (items.length == itemNames.length && items.length == N); @*/

	/*
	 * This boolean variable represents iff the vending machine has to be refilled.
	 */
	private /*@spec_public */ boolean needsRefill = false;
	
	
	
	/* 
	 * True iff the item slot 'itemSlot' exists.
	 */
	public /*@ pure @*/ boolean itemSlotExists(int itemSlot) {
		return 0 <= itemSlot && itemSlot < N;
	}
	
	/* 
	 * True iff the item slot 'itemSlot' exists and the item is in stock.
	 */
	public /*@ pure @*/ boolean itemIsInStock(int itemSlot) {
		return itemSlotExists(itemSlot) && items[itemSlot] > 0;
	}
	
	
	
	/*@ public normal_behavior
	  @ requires itemIsInStock(item);
	  @ assignable items[item];
	  @ ensures items[item] == \old(items[item]) - 1;
	  @ ensures \result == itemNames[item];
	  @
	  @ also
	  @
	  @ public exceptional_behavior 
	  @ requires !itemSlotExists(item);
	  @ assignable \nothing;
	  @ signals_only ItemNotFoundException;
	  @
	  @ also
	  @ 
	  @ public exceptional_behavior 
	  @ requires itemSlotExists(item) && !itemIsInStock(item);
	  @ assignable needsRefill;
	  @ signals_only ItemEmptyException;
	  @ signals (ItemEmptyException) needsRefill;
	  @ 
	  @ */
	public String buy(int item) throws RuntimeException {
		if (!itemSlotExists(item)) {
			throw new ItemNotFoundException();
		} else if (!itemIsInStock(item)) {
			needsRefill = true;
			throw new ItemEmptyException();
		}
		
		items[item]--;
		return itemNames[item];
	}
	
	
	
	/*@ public normal_behavior
	  @ requires !needsRefill;
	  @ assignable \nothing;
	  @
	  @ also
	  @
	  @ public normal_behavior
	  @ requires needsRefill;
	  @ assignable items[*], needsRefill;
	  @ ensures (\forall int x; 0 <= x && x < N; \old(items[x]) == 0 ? items[x] == (\old(items[x]) + 3) : items[x] == \old(items[x]));
	  @ ensures !needsRefill;
	  @ */
	public void refill() {
		if (needsRefill) {
			int x = 0;
			/*@ loop_invariant
			  @ 	(0 <= x && x <= N && needsRefill &&
			  @		(\forall int y; 0 <= y && y < x; \old(items[y]) == 0 ? items[y] == (\old(items[y]) + 3) : items[y] == \old(items[y])));
			  @	decreases N - x;
			  @ assignable items[*];
			  @*/
			while ( x < N) {
				if (items[x] == 0) {
					items[x] = items[x] + 3;
				}
				x++;
			}
			needsRefill = false;
		}
	}
}

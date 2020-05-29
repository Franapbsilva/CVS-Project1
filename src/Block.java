
/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.



Frederico Lopes, nr 42764,
Francisco Silva, nr 50654 
*/

/* There are auxiliary functions and lemmas to assist in the verification of the code below. */
/*@
	fixpoint int sum(list<int> vs) {
		switch(vs) {
			case nil: return 0;
			case cons(h, t): return (h + sum(t));
		}
	}	
	
	lemma_auto(sum(append(xs, ys))) void sum_append(list<int> xs, list<int> ys)
	requires true;
	ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
	{
		switch(xs) {
			case nil:
			case cons(h, t): sum_append(t, ys);
		}
	}	
		
	fixpoint int hashOf2(int h1, int h2) {
		return (h1^h2);
	}
	
	fixpoint int hashOf3(int h1, int h2, int h3) {
		return hashOf2(hashOf2(h1,h2),h3);
	}



	
@*/

/* These are the predicates defining representation invariants for the blockchain blocks and transactions. */

/*@	
	predicate isBlockchain(Blockchain b;) = b == null ? emp : b.head |-> ?l &*& isBlock(l,_);
 
	predicate isBlock(Block b;int h) = b == null ? h == 0 : b.BlockInv(_, _, h);
	
	

	predicate TransHash(unit a, Transaction t; int hash) =
		    t != null
		&*& TransInv(t, ?s, ?r, ?v)
		&*& hash == tansactionHash(s,r,v);
		
	predicate Positive(unit a, int v; unit n) = v>=0 &*& n == unit;
		
	fixpoint boolean ValidID(int id) {
		return 0 <= id && id < Block.MAX_ID;
	}

@*/

/* 
   The interface of the blockchain blocks. 

   It contains an instance predicate that is then defined in 
   two subclasses that define a summary block and a simple block. 
   
   This predicate defines the representation invariant for blockchain blocks.
   
*/

interface Block {
	//@ predicate BlockInv(Block p, int hp, int h);

	static final int MAX_ID = 100;

	int balanceOf(int id);
	//@ requires BlockInv(?p, ?hp, ?h) &*& ValidID(id) == true;
	//@ ensures BlockInv(p, hp, h);

	Block getPrevious();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == p;

	int getPreviousHash();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == hp;

	int hash();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == h;
}

/*
 * This class should be implemented in the course of the project development
 * with the expected operations to add and inspect the blocks
 */

class Blockchain {
	/*@ predicate BlockchainInv(Blockchain b; int[] a) = b.balances |->a 
	 &*& a != null &*& array_slice(a, 0, a.length, ?elems);
	 */

	private Block head;

	//@ ensures BlockchainInv(_) &*& isBlock(this.head)
	//@ requires array_slice_deep(balances,0,balances.length,Positive,unit,?els,?vls)
	public Blockchain(int[] balances) {
		this.head = new SummaryBlock(null, 0, balances);
	}

	/**
	 * changes the head and return the validity of the block.Valid = hash % 100 == 0
	 * 
	 * 
	 */
	public boolean addBlock(Block b)
	//@ requires BlockchainInv(?h) &*& b.isBlock() &*& b.getPrevious() == this.head;
	//@ ensures BlockchainInv(h);
	{
		boolean valid = isValid(b.hash());
		if (valid) {
			head = b;
		}
		return valid;
	}

	/**
	 * return the head of the blockchain
	 * 
	 *
	 */
	public Block getHead()
	//@ requires BlockchainInv(?h);
	//@ ensures BlockchainInv(h) &*& result == this.head;
	{
		return head;
	}

	/**
	 * a block is valid if its hash ends with two 00 - h % 100 = 0
	 * 
	 * 
	 */
	private boolean isValid(int hash)
	//@ requires BlockchainInv(?h);
	//@ ensures BlockchainInv(h);
	{
		if (hash % 100 == 0)
			return true;
		return false;
	}

}

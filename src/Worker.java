/*Frederico Lopes, nr 42764,
Francisco Silva, nr 50654 
*/
import java.util.Queue;

public class Worker {
	

	private static final int TRANSACTIONS_AMOUNT = 5;
	private int counter;
	private int random;

	public Worker() {
		//@requires true;
		//@ensures counter ==1 &*& random>=0;
		counter = 1;
		random = 2;
		
	}

	private boolean addSimpleBlock(Transaction ts[], Blockchain bChain) {
		//@requires isBlockchain(bChain);
		//@ensures true;
		Block previous = bChain.getHead();
		Block simple = new SimpleBlock(previous, random, ts);
		boolean result = bChain.addBlock(simple);
		return result;
	}

	private boolean addSummaryBlock(int[] balances, Blockchain bChain) {
		//@requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*& isBlockchain(bChain);
		//@ensures true;
		Block previous = bChain.getHead();
		Block sum = new SummaryBlock(previous, 2, balances);
		boolean result = bChain.addBlock(sum);
		return result;
	}

	private Transaction[] getTransactions(Queue<Transaction> queue) {
		//@requires true;
		//@ensures array_slice_deep(result,0,result.length,TransHash,unit,_,_);
		Transaction[] transactions = new Transaction[TRANSACTIONS_AMOUNT];
		int amount = 0;
		for (int i = 0; i < TRANSACTIONS_AMOUNT; i++) {
			//@ requires array_slice(transactions, 0, this.TRANSACTIONS_AMOUNT, ?vs)
			//@invariant i < this.TRANSACTIONS_AMOUNT &*& i>=0;
			
			if (queue.size() != 0) {
				transactions[i] = queue.remove();
				amount++;
			}
			//@ length_drop(i,vls);
			//@ take_one_more(vls,i);
			

		}
		if (amount != TRANSACTIONS_AMOUNT) {
			for (int i = 0; i < amount; i++) {
				//@ requires array_slice(transactions, 0, amount, ?vs)
				queue.add(transactions[i]);
				//@ length_drop(i,vls);
				//@ take_one_more(vls,i);

			}
			return new Transaction[0];
		}
		return transactions;
	}

	public int[] Work(Queue<Transaction> queue, int[] balances, Blockchain bChain) {
		//@requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*& isBlockchain(bChain);
		//@ensures array_slice_deep(balances,0,result.length,Positive,unit,_,_);
		random++;
		if (counter < 10) {
			Transaction[] ts = getTransactions(queue);
			if (ts.length == 0)
				return balances;
			int[] temp = makeTransactions(balances, ts);
			if (temp.length == balances.length) {
				boolean valid = addSimpleBlock(ts, bChain);
				if (valid) {
					counter++;
					return temp;
				}
			}
			for (Transaction t :ts) {
			//@requires array_slice(ts, 0, ts.length, ?vs)
				queue.add(t);
			

			}
		} else {
			addSummaryBlock(balances, bChain);
			counter = 0;
		}
		return balances;
	}

	private int[] makeTransactions(int[] balances, Transaction[] ts) {
		//@requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*& ts.length ==5 &*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_);
		//@ensures true;
		for (Transaction t : ts) {
			int sender = t.getSender();
			int receiver = t.getReceiver();
			int amount = t.getAmount();
			balances[sender] -= amount;
			balances[receiver] += amount;
		}

		for (int b : balances) {
			//@requires array_slice(balances, 0, balances.length, ?vs)
			if (b < 0)
				return new int[0];
		}
		return balances;
	}

}

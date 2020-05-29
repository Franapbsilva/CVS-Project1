
/*Frederico Lopes, nr 42764,
Francisco Silva, nr 50654 
*/
import java.util.Queue;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

public class Worker {

	private static final int TRANSACTIONS_AMOUNT = 5;
	private Queue<Transaction> queue;
	private int[] balances;
	private Blockchain bChain;
	private int[] random;
	private Thread t;
	private boolean summary;
	ReentrantLock mon;

	public Worker(Queue<Transaction> queue, int[] balances, Blockchain bChain, int[] random) {
		
		this.queue = queue;
		this.balances = balances;
		this.bChain = bChain;
		this.random = random;
		summary = false;
		t = new Thread(this::work);
		t.start();
		mon = new ReentrantLock();
	}

	public Worker(int[] balances, Blockchain bChain, int[] random) {
		this.balances = balances;
		this.bChain = bChain;
		this.random = random;
		summary = true;
		t = new Thread(this::work);
		t.start();
		mon = new ReentrantLock();
	}

	private boolean addSimpleBlock(Transaction ts[], Blockchain bChain) // @ requires isBlockchain(bChain) &*& random>=0
																		// &*& summary==false;
	// @ ensures true;
	{
		// @ request permission to the shared state
		mon.lock();
		Block previous = bChain.getHead();
		Block simple = new SimpleBlock(previous, random[0], ts);
		boolean result = bChain.addBlock(simple);
		mon.unlock();
		// @ release ownership of the shared state
		return result;
	}

	private boolean addSummaryBlock(int[] balances, Blockchain bChain)
	/*
	 * @ requires isBlockchain(bChain) &*& random>=0 &*&
	 * array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*&
	 * isBlockchain(bChain) &*& summary==true;
	 */
	// @ ensures true;
	{
		mon.lock();
		// @ request permission to the shared state
		Block previous = bChain.getHead();
		Block sum = new SummaryBlock(previous, random[0], balances);
		boolean result = bChain.addBlock(sum);
		mon.unlock();
		// @ release ownership of the shared state
		return result;
	}

	private Transaction[] getTransactions(Queue<Transaction> queue)
	// @ requires true;
	// @ ensures array_slice_deep(result,0,result.length,TransHash,unit,_,_);
	{
		// @ request permission to the shared state
		mon.lock();
		Transaction[] transactions = new Transaction[TRANSACTIONS_AMOUNT];
		int amount = 0;
		while (amount < TRANSACTIONS_AMOUNT) {
			// @ requires array_slice(transactions, 0, this.TRANSACTIONS_AMOUNT, ?vs)
			// @invariant i < this.TRANSACTIONS_AMOUNT &*& i>=0;

			if (queue.size() != 0) {
				transactions[amount] = queue.remove();
				amount++;
			}
			// @ length_drop(i,vls);
			// @ take_one_more(vls,i);

		}
		mon.unlock();
		// @ release ownership of the shared state
		return transactions;
	}

	private void work()
	// @ requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*&
	// isBlockchain(bChain);
	// @ ensures array_slice_deep(balances,0,result.length,Positive,unit,_,_);
	{

		while (true) {
			

			// @ request permission to the shared state
			mon.lock();
			if (summary) {
				while (random[0] % 10 != 0) {

				}
				addSummaryBlock(balances, bChain);
				random[0]++;
			} else {
				while (random[0] % 10 == 0) {
					if (queue.isEmpty()) {

						Transaction[] ts = getTransactions(queue);
						boolean result = addSimpleBlock(ts, bChain);
						if (result) {
							int[] temp = new int[balances.length];
							for (int i = 0; i < balances.length; i++) {
								temp[i] = balances[i];
							}
							makeTransactions(temp, ts);
							if (isBalanceValid(temp)) {
								makeTransactions(balances, ts);
								random[0]++;

							}
							for (Transaction t : ts) {
								// @requires array_slice(ts, 0, ts.length, ?vs)
								queue.add(t);
							}

						}
						for (Transaction t : ts) {
							// @requires array_slice(ts, 0, ts.length, ?vs)
							queue.add(t);

						}
					}
				}
			}
			mon.unlock();
			// @ release ownership of the shared state

		}

	}

	private void makeTransactions(int[] array, Transaction[] ts)
	// @requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*&
	// ts.length ==5 &*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_);
	// @ensures true;
	{
		// @ request permission to the shared state
		mon.lock();
		for (Transaction t : ts) {
			int sender = t.getSender();
			int receiver = t.getReceiver();
			int amount = t.getAmount();
			array[sender] -= amount;
			array[receiver] += amount;
		}
		mon.unlock();
		// @ release ownership of the shared state
	}

	private boolean isBalanceValid(int[] balances) {
		// @ request permission to the shared state
		mon.lock();
		for (int b : balances) {
			// @requires array_slice(balances, 0, balances.length, ?vs)
			if (b < 0)
				return false;
		}
		mon.unlock();
		// @ release ownership of the shared state
		return true;
	}

}

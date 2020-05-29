
/*Frederico Lopes, nr 42764,
Francisco Silva, nr 50654 
*/
import java.util.Queue;
import java.util.concurrent.locks.*;

	/*@
	  lemma void mod(int x, int y, int rest);
		requires abs(y) > 1 && abs(rest) != abs(y);
		ensures (x + rest) % y != x % y;
	@*/
public class Worker {
	/*
	 * @ predicate_ctor Worker_shared_state (Worker w)() = w.TRANSACTION_AMMOUNT |->
	 * ?m &*& m == 5;
	 * 
	 * @
	 */

	/*
	 * @ predicate WorkerInv(Worker w;List l, int[] balances, Blockchain b, int[] r,
	 * Thread t, boolean s) = w.queue |-> l &*& w.balances |-> balances &*& w.bChain
	 * |-> b &*& this.random |-> r &*& w.t |-> t &*& w.s |-> summary &*&;
	 * 
	 * @
	 */
	private static final int TRANSACTIONS_AMOUNT = 5;
	private Queue<Transaction> queue;
	private int[] balances;
	private Blockchain bChain;
	private int[] random;
	private Thread t;
	private boolean summary;
	ReentrantLock mon;

	public Worker(Queue<Transaction> queue, int[] balances, Blockchain bChain, int[] random, boolean isSummary)
	/*@ requires WorkInv(this) 
			&*& array_slice_deep(balances,0,balances.length,Positive,unit,?els,?vls);
	@*/
	// @ ensures true;
	{
		this.queue = queue;
		this.balances = balances;
		this.bChain = bChain;
		this.random = random;
		summary = isSummary;
		t = new Thread(this::work);
		t.start();
		// @ close Worker_shared_state(this);
		// @ close enter_lck(1, Worker_shared_state(this));
		mon = new ReentrantLock();
		// @ assert lck(mon, 1, Worker_shared_state(this));
		// @ close WorkerInv(this)
	}

	private boolean addSimpleBlock(Transaction ts[], Blockchain bChain)
	/*
	 * @ requires isBlockchain(bChain) &*& random>=0 &*& summary==false;
	 */
	// @ ensures true;
	{
		// @ open Worker_shared_state(this)();
		mon.lock();
		Block previous = bChain.getHead();
		Block simple = new SimpleBlock(previous, random[0], ts);
		boolean result = bChain.addBlock(simple);
		mon.unlock();
		// @ close Worker_shared_state(this)();
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
		// @ open Worker_shared_state(this)();
		Block previous = bChain.getHead();
		Block sum = new SummaryBlock(previous, random[0], balances);
		boolean result = bChain.addBlock(sum);
		mon.unlock();
		// @ close Worker_shared_state(this)();
		return result;
	}

	private synchronized Transaction[] getTransactions(Queue<Transaction> queue)
	// @ requires true;
	// @ ensures array_slice_deep(result,0,result.length,TransHash,unit,_,_);
	{
		// @ open Worker_shared_state(this)();
		mon.lock();
		Transaction[] transactions = new Transaction[TRANSACTIONS_AMOUNT];
		int amount = 0;
		while (amount < TRANSACTIONS_AMOUNT) {
			// @ requires array_slice(transactions, 0, this.TRANSACTIONS_AMOUNT, ?vs);
			// @ invariant i < this.TRANSACTIONS_AMOUNT &*& i>=0;

			try {
				if (!queue.isEmpty()) {
					transactions[amount] = queue.remove();

					amount++;

				}
			} catch (Exception e) {

			}
			// @ length_drop(i,vls);
			// @ take_one_more(vls,i);

		}
		mon.unlock();
		// @ close Worker_shared_state(this)();
		return transactions;
	}

	private void work()
	/*
	 * @ requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_) &*&
	 * isBlockchain(bChain);
	 */
	// @ ensures array_slice_deep(balances,0,result.length,Positive,unit,_,_);
	{

		while (true) {

			// @ open Worker_shared_state(this)();
			mon.lock();
			if (summary) {
				while (random[0] % 10 != 0) {
					//@ mod(this.r, 10, 0);
					// do nothing
				}

				addSummaryBlock(balances, bChain);
				random[0]++;

			} else {
				while (random[0] % 10 == 0) {
					//@ mod(this.r, 10, 0);
					// do nothing
				}

				if (!queue.isEmpty()) {

					Transaction[] ts = getTransactions(queue);
					boolean result = addSimpleBlock(ts, bChain);
					if (result) {
						int[] temp = new int[balances.length];
						for (int i = 0; i < balances.length; i++) {
							temp[i] = balances[i];
							//@ close Worker_shared_state(this)();
						}
						makeTransactions(temp, ts);
						if (isBalanceValid(temp)) {
							makeTransactions(balances, ts);
							ts = new Transaction[TRANSACTIONS_AMOUNT];
							random[0]++;
							//@ close Worker_shared_state(this)();
						}
						for (Transaction t : ts) {
							//@ requires array_slice(ts, 0, ts.length, ?vs);
							queue.add(t);
						}

					}
					for (Transaction t : ts) {
						//@ requires array_slice(ts, 0, ts.length, ?vs);
						queue.add(t);

					}
				}

			}
			mon.unlock();
			// @ close WorkerInv(this);
		}

	}

	private void makeTransactions(int[] array, Transaction[] ts)
	/*@ requires array_slice_deep(balances,0,balances.length,Positive,unit,_,_)
	  	&*& ts.length ==5 &*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_);
	 @*/
	// @ ensures true;
	{
		// @ open Worker_shared_state(this)();
		mon.lock();
		for (Transaction t : ts) {
			int sender = t.getSender();
			int receiver = t.getReceiver();
			int amount = t.getAmount();
			array[sender] -= amount;
			array[receiver] += amount;
			//@ close Worker_shared_state(this)();
		}
		mon.unlock();
		// @ close WorkerInv(this);;
	}

	private boolean isBalanceValid(int[] balances) {
		// @ open Worker_shared_state(this)();
		mon.lock();
		for (int b : balances) {
			// @requires array_slice(balances, 0, balances.length, ?vs)
			if (b < 0)
				return false;
		}
		mon.unlock();
		// @ close WorkerInv(this);
		return true;
	}

}

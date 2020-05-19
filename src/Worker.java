import java.util.Queue;

public class Worker {

	private static final int TRANSACTIONS_AMOUNT = 5;
	private int counter;

	public Worker() {
		counter = 1;
	}

	private boolean addSimpleBlock(Transaction ts[], Blockchain bChain) {
		Block previous = bChain.getHead();
		Block simple = new SimpleBlock(previous, 2, ts);
		boolean result = bChain.addBlock(simple);
		return result;
	}

	private boolean addSummaryBlock(int[] balances, Blockchain bChain) {
		Block previous = bChain.getHead();
		Block sum = new SummaryBlock(previous, 2, balances);
		boolean result = bChain.addBlock(sum);
		return result;
	}

	private Transaction[] getTransactions(Queue<Transaction> queue) {
		Transaction[] transactions = new Transaction[TRANSACTIONS_AMOUNT];
		int amount = 0;
		for (int i = 0; i < TRANSACTIONS_AMOUNT; i++) {
			if (queue.size() != 0) {
				transactions[i] = queue.remove();
				amount++;
			}

		}
		if (amount != TRANSACTIONS_AMOUNT) {
			for (int i = 0; i < amount; i++) {
				queue.add(transactions[i]);

			}
			return new Transaction[0];
		}
		return transactions;
	}

	public void Work(Queue<Transaction> queue, int[] balances, Blockchain bChain) {
		if(counter<10) {
			Transaction[] ts = getTransactions(queue);
			if(ts.length==0) return;
			addSimpleBlock(ts,bChain);
			counter++;
		}else {
			addSummaryBlock(balances, bChain);
			counter = 0;
		}
	}

}

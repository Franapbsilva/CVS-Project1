import java.util.Queue;

public class Worker {

	private static final int TRANSACTIONS_AMOUNT = 5;
	private int counter;
	private int random;

	public Worker() {
		counter = 1;
		random = 2;
		
	}

	private boolean addSimpleBlock(Transaction ts[], Blockchain bChain) {
		Block previous = bChain.getHead();
		Block simple = new SimpleBlock(previous, random, ts);
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

	public int[] Work(Queue<Transaction> queue, int[] balances, Blockchain bChain) {
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
				queue.add(t);

			}
		} else {
			addSummaryBlock(balances, bChain);
			counter = 0;
		}
		return balances;
	}

	private int[] makeTransactions(int[] balances, Transaction[] ts) {
		for (Transaction t : ts) {
			int sender = t.getSender();
			int receiver = t.getReceiver();
			int amount = t.getAmount();
			balances[sender] -= amount;
			balances[receiver] += amount;
		}

		for (int b : balances) {
			if (b < 0)
				return new int[0];
		}
		return balances;
	}

}

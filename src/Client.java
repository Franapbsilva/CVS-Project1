import java.util.LinkedList;
import java.util.Queue;

public class Client {
	Queue<Transaction> transactionQueue;
	Worker singleWorker;
	int[] balances;
	Blockchain bChain;
	
	public Client(int[] balances) {
		transactionQueue = new LinkedList<Transaction>();
		singleWorker = new Worker();
		this.balances = balances;
		bChain = new Blockchain(balances);
		
	}
	public void addTransactionToQueue(Transaction t, Queue<Transaction> queue) {
		queue.add(t);
	}

	
}

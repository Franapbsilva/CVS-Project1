
/*Frederico Lopes, nr 42764,
Francisco Silva, nr 50654 
*/
import java.util.Queue;
import java.util.Scanner;
import java.util.concurrent.LinkedBlockingQueue;

public class Client {
	public final static int WORKERS_AMOUNT = 5;

	public static int[] generateNewBalances() {
		int length = (int) Math.floor(Math.random() * 100) + 2;
		int[] newBalances = new int[length];
		for (int i = 0; i < length; i++) {
			newBalances[i] = (int) Math.floor(Math.random() * 1000);
		}
		return newBalances;
	}

	public static void addTransactionToQueue(Scanner s, Queue<Transaction> queue) {
		int sender = s.nextInt();
		int receiver = s.nextInt();
		int amount = s.nextInt();
		Transaction t = new Transaction(sender, receiver, amount);
		
		queue.add(t);
	}

	public static void main(String[] args) 
	// @ requires true
	// @ ensures true
	{
		
		Queue<Transaction> transactionQueue = new LinkedBlockingQueue<Transaction>();
		int[] balances = generateNewBalances();
		Blockchain bChain = new Blockchain(balances);
		Scanner scan = new Scanner(System.in);
		PoolOfWorkers worker = new PoolOfWorkers(WORKERS_AMOUNT, transactionQueue, balances, bChain);
		// @ assert PoolOfWorkersInv
		while(true) {
			addTransactionToQueue(scan, transactionQueue);
			
			
		}

		

	}

}

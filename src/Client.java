
/*Frederico Lopes, nr 42764,
Francisco Silva, nr 50654 
*/
import java.util.LinkedList;
import java.util.Queue;
import java.util.Scanner;

public class Client {

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

	public static void main(String[] args) {
		Queue<Transaction> transactionQueue = new LinkedList<Transaction>();
		Worker singleWorker = new Worker();
		int[] balances = generateNewBalances();
		Blockchain bChain = new Blockchain(balances);
		Scanner scan = new Scanner(System.in);
		while (true) {
			addTransactionToQueue(scan, transactionQueue);
			balances = singleWorker.Work(transactionQueue, balances, bChain);
		}

	}

}

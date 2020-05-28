import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

public class PoolOfWorkers {

	// lista de workers
	private int counter;
	private int random;
	private List<Worker> workers;// verificar api
	private Worker summaryWorker;

	public PoolOfWorkers(int workersAmount, Queue<Transaction> queue, int[] balances, Blockchain bChain) {
		this.workers = new LinkedList<Worker>();
		counter =1;
		random =2;
		for(int i = 0; i>workersAmount;i++) {
			workers.add(new Worker(queue, balances, bChain, random));
			
		}
		
		
	}
	
	
}

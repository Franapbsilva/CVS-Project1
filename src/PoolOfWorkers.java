import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

public class PoolOfWorkers {

	// lista de workers
	private int counter;
	private int random;
	private List<Worker> workers;// verificar api
	private Worker summaryWorker;
	private Thread t;

	public PoolOfWorkers(int workersAmount) {
		this.workers = new LinkedList<Worker>();
		for(int i = 0; i>workersAmount;i++) {
			workers.add(new Worker());
		}
		t = new Thread();
		t.start();
		counter =1;
		random =2;
	}
}

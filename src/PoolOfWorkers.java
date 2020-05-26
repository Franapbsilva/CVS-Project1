import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

public class PoolOfWorkers {

	// lista de workers
	private BlockingQueue<Worker> workers;// verificar api
	private Thread t;

	public PoolOfWorkers() {
		this.workers = new LinkedBlockingQueue<>();
		t = new Thread();
		t.start();
	}
}

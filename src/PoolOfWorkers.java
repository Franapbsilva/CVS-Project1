import java.util.LinkedList;
import java.util.List;
import java.util.Queue;


public class PoolOfWorkers {
	/*@ predicate PoolOfWorkersInv(PoolOfWorkers pol;int[] c, List w) = 
	  		pol.c |-> counter &*& pol.w |-> workers;
	 @*/

	// lista de workers
	private int[] counter;
	private List<Worker> workers;

	public PoolOfWorkers(int workersAmount, Queue<Transaction> queue, int[] balances, Blockchain bChain)
	/*@ requires PoolOfWorkersInv(this) 
			&*& array_slice_deep(balances,0,balances.length,Positive,unit,?els,?vls)
			&*& isBlockChain(this.b,_);
	@*/
	//@ ensures true;
	{
		this.workers = new LinkedList<Worker>();
		counter = new int[1];
		counter[0] = 1;
		for(int i = 0; i<workersAmount;i++) {
			workers.add(new Worker(queue, balances, bChain, counter, false));
			//@ assert WorkerInv(queue, balances, bChain, counter, false);
		}
		workers.add(new Worker(queue, balances, bChain, counter, true));
		//@ assert WorkerInv(queue, balances, bChain, counter, true);
	}
	
	
	
}

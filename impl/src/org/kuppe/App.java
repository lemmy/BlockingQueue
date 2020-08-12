package org.kuppe;

import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import tlc2.tool.TLAPlusExecutor;
import tlc2.tool.TLAPlusExecutor.Mapping;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.SetEnumValue;

public class App {

	public static void main(String[] args) throws InterruptedException {
		// The magic sauce.
		final TLAPlusExecutor executor = new TLAPlusExecutor("BlockingQueueSplit", "BlockingQueueSplit"); // BQS.tla, BQS.cfg
		
		final IBlockingQueue<String> queue = new TLABlockingQueue<>(executor);

		// The set of executing tasks.
		final Collection<Callable<Void>> tasks = new HashSet<>();
		
		// Create a Java Consumer (Producer) for every model value for the TLA+ constant
		// Consumers (Producers).
		((SetEnumValue) executor.getConstant("Consumers").toSetEnum()).elements().forEach(e -> {
			final ModelValue mv = (ModelValue) e;
			// Map a condition - derived from the executor's lock - to each model value
			// that represents a consumer process in TLA+.  The condition is how the
			// TLAPlusExecutor controls the Java thread.
			mv.setData(executor.getLock().newCondition());
			// Map the current Java thread Consumer to its corresponding TLA+ action (TLC
			// creates an action instance for Put and Get for each TLA+ process).
			final Mapping map = executor.map("Get", "t", e);
			
			tasks.add(new Consumer(map, e.toString(), queue));
		});
		((SetEnumValue) executor.getConstant("Producers").toSetEnum()).elements().forEach(e -> {
			final ModelValue mv = (ModelValue) e;
			// Map a condition - derived from the executor's lock - to each model value
			// that represents a consumer process in TLA+.  The condition is how the
			// TLAPlusExecutor controls the Java thread.
			mv.setData(executor.getLock().newCondition());
			// Map queue.put below to TLA+ Put action. Map this thread to t param of TLA+
			// Put action. Indicate that queue.put is going to pass the 'd' param of the
			// TLA+ action.
			final Mapping map = executor.map("Put", "t", e, "d");
			
			tasks.add(new Producer(map, e.toString(), queue));
		});
		
		// Run all tasks concurrently.
		final ExecutorService pool = Executors.newCachedThreadPool();
		pool.invokeAll(tasks);
		
		// This will never be reached.
		pool.shutdown();
		pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
	}
}

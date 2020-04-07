package org.kuppe;

import java.util.concurrent.Callable;

import tlc2.tool.TLAPlusExecutor.Mapping;

class Consumer implements Callable<Void> {
	
	private final String name;
	private final IBlockingQueue<String> queue;
	private final Mapping m;

	public Consumer(final String name, final IBlockingQueue<String> queue) {
		this.name = name;
		this.queue = queue;
		// Register this Consumer with the TLA+ implementation of the blocking queue
		// (no-op for native impl). It essentially maps the java operation to its TLA+
		// action counterpart.
		this.m = this.queue.register("Get", "t", name);
	}

	@Override
	public Void call() throws Exception {
		while (true) {
			final Object take = queue.take(m);
			if (take == null) {
				throw new NullPointerException();
			}
			System.out.printf("%s took %s\n", name, take);
		}
	}
}

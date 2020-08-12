package org.kuppe;

import java.util.concurrent.Callable;

import tlc2.tool.TLAPlusExecutor.Mapping;

class Consumer implements Callable<Void> {
	
	private final String name;
	private final IBlockingQueue<String> queue;
	private final Mapping m;

	public Consumer(Mapping m, final String name, final IBlockingQueue<String> queue) {
		this.m = m;
		this.name = name;
		this.queue = queue;
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

package org.kuppe;

import java.util.concurrent.Callable;

import tlc2.tool.TLAPlusExecutor.Mapping;

class Producer implements Callable<Void> {

	private final IBlockingQueue<String> queue;
	private final String name;
	private final Mapping mapping;

	public Producer(final Mapping m, final String name, IBlockingQueue<String> queue) {
		mapping = m;
		this.name = name;
		this.queue = queue;
	}

	@Override
	public Void call() throws Exception {
		long i = 1;
		while (true) {
			queue.put(mapping, name + "_" + i++);
//				System.out.printf("%s put %s\n", name, string);
		}
	}
}
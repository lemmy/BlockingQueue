package org.kuppe;

import java.util.concurrent.Callable;

import tlc2.tool.TLAPlusExecutor.Mapping;

class Producer implements Callable<Void> {

	private final IBlockingQueue<String> queue;
	private final String name;
	private final Mapping mapping;

	public Producer(final String name, final IBlockingQueue<String> queue) {
		this.name = name;
		this.queue = queue;
		// Map queue.put below to TLA+ Put action. Map this thread to t param of TLA+
		// Put action. Indicate that queue.put is going to pass the 'd' param of the
		// TLA+ action.
		this.mapping = this.queue.register("Put", "t", name, "d");
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
package org.kuppe;

import java.util.concurrent.Callable;

class Producer implements Callable<Void> {

	private final BlockingQueue<String> queue;
	private final String name;

	public Producer(final String name, final BlockingQueue<String> queue) {
		this.name = name;
		this.queue = queue;
	}

	@Override
	public Void call() throws Exception {
		while (true) {
			queue.put(name);
		}
	}
}
package org.kuppe;

import java.util.concurrent.Callable;

class Consumer implements Callable<Void> {
	
	private final BlockingQueue<String> queue;

	public Consumer(final BlockingQueue<String> queue) {
		this.queue = queue;
	}

	@Override
	public Void call() throws Exception {
		long l = 0l;
		while (true) {
			l++;
			final Object take = queue.take();
			if (take == null) {
				throw new NullPointerException();
			}
			if (l % 1000000 == 0) {
				System.out.printf("Throughput %s\n", l);
			}
		}
	}
}

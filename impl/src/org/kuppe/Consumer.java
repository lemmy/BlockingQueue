package org.kuppe;

import java.util.Random;
import java.util.concurrent.Callable;

class Consumer implements Callable<Void> {
	
	private static final int sleepCons = 23;
	
	private final Random rand = new Random();
	private final BlockingQueue<String> queue;

	public Consumer(final BlockingQueue<String> queue) {
		this.queue = queue;
	}

	@Override
	public Void call() throws Exception {
		while (true) {
			final Object take = queue.take();
			if (take == null) {
				throw new NullPointerException();
			}
			System.out.printf("C took %s\n", take);
			Thread.sleep(rand.nextInt(sleepCons));
		}
	}
}

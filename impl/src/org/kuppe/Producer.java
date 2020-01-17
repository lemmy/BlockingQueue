package org.kuppe;

import java.util.Random;
import java.util.concurrent.Callable;

class Producer implements Callable<Void> {

	private final int sleepProd = 42;
	private final Random rand = new Random();

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
			System.out.printf("P put %s\n", name);
			Thread.sleep(rand.nextInt(sleepProd));
		}
	}
}
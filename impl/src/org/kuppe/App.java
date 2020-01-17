package org.kuppe;

import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class App {

	public static void main(String[] args) throws InterruptedException {
        final Configuration conf = new Configuration(args);

		final int k = conf.bufCapacity;
		final BlockingQueue<String> queue = new BlockingQueue<>(k);

		// The set of executing tasks.
		final Collection<Callable<Void>> tasks = new HashSet<>();
		for (int i = 0; i < conf.producers; i++) {
			tasks.add(new Producer(Integer.toString(tasks.size()), queue));
		}
		for (int i = 0; i < conf.consumers; i++) {
			tasks.add(new Consumer(queue));
		}
		
		// Run all tasks concurrently.
		final ExecutorService pool = Executors.newCachedThreadPool();
		pool.invokeAll(tasks);
		
		// This will never be reached.
		pool.shutdown();
		pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
	}

	private static class Configuration {
		public final int bufCapacity;
		public final int producers;
		public final int consumers;

		public Configuration(String args[]) {
			if (args.length == 3) {
				this.bufCapacity = Integer.parseInt(args[0]);
				this.producers = Integer.parseInt(args[1]);
				this.consumers = Integer.parseInt(args[2]);
			} else {
				this.bufCapacity = 3;
				this.producers = 4;
				this.consumers = 3;
			}
		}
	}
}

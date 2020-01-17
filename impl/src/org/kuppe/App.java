package org.kuppe;

import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class App {

	public static void main(String[] args) throws InterruptedException {
		final int k = 3;
		final BlockingQueue<String> queue = new BlockingQueue<>(k);

		// The set of executing tasks.
		final Collection<Callable<Void>> tasks = new HashSet<>();
		tasks.add(new Producer(Integer.toString(tasks.size()), queue));
		tasks.add(new Producer(Integer.toString(tasks.size()), queue));
		tasks.add(new Producer(Integer.toString(tasks.size()), queue));
		tasks.add(new Producer(Integer.toString(tasks.size()), queue));
		tasks.add(new Consumer(queue));
		tasks.add(new Consumer(queue));
		tasks.add(new Consumer(queue));
		
		// Run all tasks concurrently.
		final ExecutorService pool = Executors.newCachedThreadPool();
		pool.invokeAll(tasks);
		
		// This will never be reached.
		pool.shutdown();
		pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
	}
}

package org.kuppe;

public final class BlockingQueue<E> {

	private final E[] store;
	
	private int head;
	private int tail;
	private int size;

	@SuppressWarnings("unchecked")
	public BlockingQueue(final int capacity) {
		this.store = (E[]) new Object[capacity];
	}

	/**
	 * Add the given element to this queue waiting if necessary for space to become
	 * available.
	 * 
	 * @see {@link BlockingQueue#take()}.
	 */
	public synchronized void put(final E e) throws InterruptedException {
		while (isFull()) {
			System.out.println("Buffer full; P waits");
			wait();
			System.out.println("P notified");
		}
		notify();
		
		// Add e and do bookkeeping.
		append(e);
	}

	/**
	 * Remove an element E from this queue, waiting if necessary until an element
	 * becomes available.
	 * 
	 * @see {@link BlockingQueue#put(Object)}.
	 */
	public synchronized E take() throws InterruptedException {
		while (isEmpty()) {
			System.out.println("Buffer empty; C waits");
			wait();
			System.out.println("C notified");
		}
		notify();
		
		// Remove e and do bookkeeping.
		return head();
	}
	
	
	//****** auxiliary methods ******//

	private void append(final E e) {
		store[tail] = e;
		tail = next(tail);
		size++;
	}

	private E head() {
		final E e = store[head];
		store[head] = null;
		head = next(head);
		size--;
		return e;
	}

	private int next(final int x) {
		return (x + 1) % store.length;
	}

	/**
	 * @return true if this buffer has reached its capacity defined during
	 *         instantiation.
	 */
	private boolean isFull() {
		return size == this.store.length;
	}

	/**
	 * @return true iff this buffer contains no elements E.
	 */
	private boolean isEmpty() {
		return size == 0;
	}
}
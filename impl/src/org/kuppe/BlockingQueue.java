package org.kuppe;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import org.kuppe.App2TLA.BufferDeqEvent;
import org.kuppe.App2TLA.BufferEnqEvent;
import org.kuppe.App2TLA.BufferWaitEvent;

public final class BlockingQueue<E> {

	private final E[] store;
	
	private final ReentrantLock lock;
	private final Condition waitC;
	private final Condition waitP;
	
	private int head;
	private int tail;
	private int size;

	@SuppressWarnings("unchecked")
	public BlockingQueue(final int capacity) {
		this.store = (E[]) new Object[capacity];
		
		// see BlockingQueueSplit.tla
		this.lock = new ReentrantLock();
		this.waitC = lock.newCondition();
		this.waitP = lock.newCondition();
	}

	/**
	 * Add the given element to this queue waiting if necessary for space to become
	 * available.
	 * 
	 * @see {@link BlockingQueue#take()}.
	 */
	public void put(final E e) throws InterruptedException {
		final ReentrantLock lock = this.lock;
		lock.lock();
		try {
			while (isFull()) {
				new BufferWaitEvent("p").commit();
				System.out.println("Buffer full; P waits");
				waitP.await();
				System.out.println("P notified");
			}
			waitC.signal();

			// Add e and do bookkeeping.
			new BufferEnqEvent().commit();
			append(e);
		} finally {
			lock.unlock();
		}
	}

	/**
	 * Remove an element E from this queue, waiting if necessary until an element
	 * becomes available.
	 * 
	 * @see {@link BlockingQueue#put(Object)}.
	 */
	public E take() throws InterruptedException {
        final ReentrantLock lock = this.lock;
        lock.lock();
        try {
    		while (isEmpty()) {
    			new BufferWaitEvent("c").commit();
    			System.out.println("Buffer empty; C waits");
    			waitC.await();
    			System.out.println("C notified");
    		}
    		waitP.signal();
    		
    		// Remove e and do bookkeeping.
    		new BufferDeqEvent().commit();
    		return head();
        } finally {
            lock.unlock();
        }
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
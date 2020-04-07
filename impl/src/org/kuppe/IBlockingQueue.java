package org.kuppe;

import tlc2.tool.TLAPlusExecutor.Mapping;

public interface IBlockingQueue<E> {

	/**
	 * Add the given element to this queue waiting if necessary for space to become
	 * available.
	 * 
	 * @see {@link BlockingQueue#take()}.
	 */
	void put(E e) throws Exception;

	/**
	 * Remove an element E from this queue, waiting if necessary until an element
	 * becomes available.
	 * 
	 * @see {@link BlockingQueue#put(Object)}.
	 */
	E take() throws Exception;

	// TLA+ specific stuff below.
	
	void put(Mapping m, E e) throws Exception;

	E take(Mapping m) throws Exception;

	default Mapping register(String s1, String s2, String s3, String... params) {
		//no-op
		return null;
	}
}
package org.kuppe;

import tlc2.tool.TLAPlusExecutor;
import tlc2.tool.TLAPlusExecutor.Mapping;
import tlc2.value.impl.StringValue;

public class TLABlockingQueue<E> implements IBlockingQueue<E> {

	private final TLAPlusExecutor executor;

	public TLABlockingQueue(final TLAPlusExecutor executor) {
		this.executor = executor;
	}

	@Override
	public void put(E e) throws Exception {
		throw new UnsupportedOperationException("Use put(String, String)");
	}

	@Override
	public E take() throws Exception {
		throw new UnsupportedOperationException("Use take(String)");
	}

	@Override
	public void put(final Mapping id, final E e) throws Exception {
		this.executor.step(id.set("d", new StringValue(e.toString())));
	}

	@SuppressWarnings("unchecked")
	@Override
	public E take(final Mapping id) throws Exception {
		return (E) this.executor.step(id);
	}
}

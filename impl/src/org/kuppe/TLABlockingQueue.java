package org.kuppe;

import java.util.concurrent.Callable;
import java.util.concurrent.locks.Condition;

import tlc2.overrides.TLAPlusCallable;
import tlc2.tool.TLAPlusExecutor;
import tlc2.tool.TLAPlusExecutor.Mapping;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;

public class TLABlockingQueue<E> implements IBlockingQueue<E> {

	private final TLAPlusExecutor executor;

	public TLABlockingQueue() {
		this.executor = new TLAPlusExecutor("BlockingQueueSplit", "BlockingQueueSplit");
	}

	@Override
	public TLAPlusExecutor.Mapping register(final String actionName, final String parameterName, final String modelValue, final String...params) {
		// Map a condition - derived from the executor's lock - with each model value
		// that represents a process in TLA+.
		final ModelValue t = (ModelValue) ModelValue.make(modelValue);
		t.setData(this.executor.getLock().newCondition());

		// Map the current Java thread (Producer or Consumer) to its corresponding
		// TLA+ action (TLC creates an action instance for Put and Get for each
		// TLA+ process).
		return this.executor.map(actionName, parameterName, t, params);
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

	@TLAPlusCallable(definition = "JWait", module = "BlockingQueueSplit")
	public static Callable<?> jWait(final Value t) {
		return () -> {
			((Condition) t.getData()).await();
			return null;
		};
	}

	@TLAPlusCallable(definition = "JSignalReturn", module = "BlockingQueueSplit")
	public static Callable<?> jSignalReturn(final Value t, final Value d) {
		return () -> {
			((Condition) t.getData()).signal();
			return d.toString();
		};
	}

	@TLAPlusCallable(definition = "JReturn", module = "BlockingQueueSplit")
	public static Callable<?> jReturn(final Value d) {
		return () -> {
			return d.toString();
		};
	}
}

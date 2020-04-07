package tlc2.overrides;

import java.util.concurrent.Callable;
import java.util.concurrent.locks.Condition;

import org.kuppe.TLABlockingQueue;

import tlc2.value.impl.Value;

public class TLCOverrides implements ITLCOverrides {
	
	//---- Java module overrides for the three operators defined in the BQS spec ----//

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

	@Override
	public Class[] get() {
		// Convention how TLC will load this thing.
		return new Class[] { TLCOverrides.class };
	}
}

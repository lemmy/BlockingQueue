package tlc2.overrides;

import org.kuppe.TLABlockingQueue;

public class TLCOverrides implements ITLCOverrides {

	@Override
	public Class[] get() {
		return new Class[] { TLABlockingQueue.class };
	}
}

package org.kuppe;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;
import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;
import tlc2.value.ValueOutputStream;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class App2TLA2bak {

	@Label("Buffer Deq Operation")
	@Name("app.bufDeqOp")
	@Category("MyApp")
	@StackTrace(false)
	static class BufferDeqEvent extends jdk.jfr.Event {
	}

	@Label("Buffer Deq Operation")
	@Name("app.bufEnqOp")
	@Category("MyApp")
	@StackTrace(false)
	static class BufferEnqEvent extends jdk.jfr.Event {
	}

	@Label("Buffer Wait Operation")
	@Name("app.bufWaitOp")
	@Category("MyApp")
	@StackTrace(false)
	static class BufferWaitEvent extends jdk.jfr.Event {

		@Label("(p)roducer or (c)onsumer")
		String type;

		public BufferWaitEvent(String type) {
			this.type = type;
		}
	}

	public static void main(final String[] args) throws IOException {
		final List<RecordedEvent> recordedEvents = RecordingFile
				.readAllEvents(Paths.get(args.length > 0 ? args[0] : "app.jfr"));

		// Order events chronologically based on the system's clock (that hopefully has
		// sufficient precision).
		// TODO: Logical clock instead of real/global clock.
		recordedEvents.sort(new Comparator<RecordedEvent>() {
			@Override
			public int compare(RecordedEvent o1, RecordedEvent o2) {
				return o1.getStartTime().compareTo(o2.getStartTime());
			}
		});

		serializeTrace(recordedEvents.stream().filter(e -> e.getEventType().getName().startsWith("app."))
				.collect(Collectors.toList()), Paths.get(args.length > 1 ? args[1] : "Trace.bin"));
	}

	private static void serializeTrace(final List<RecordedEvent> events, final Path out) throws IOException {
		System.out.printf("Parsing %s events to %s.\n", events.size(), out);

		final UniqueString op = UniqueString.uniqueStringOf("op");
		final RecordValue deq = new RecordValue(op, new StringValue("d"));
		final RecordValue enq = new RecordValue(op, new StringValue("e"));

		final StringValue w = new StringValue("w");
		final UniqueString waiter = UniqueString.uniqueStringOf("waiter");
		final RecordValue waitP = new RecordValue(new UniqueString[] { op, waiter },
				new Value[] { w, new StringValue("p") }, false);
		final RecordValue waitC = new RecordValue(new UniqueString[] { op, waiter },
				new Value[] { w, new StringValue("c") }, false);

		final Value[] v = new Value[events.size()];
		int i = 0;
		
		for (RecordedEvent event : events) {
			if (event.getEventType().getName().equals("app.bufDeqOp")) {
				v[i++] = deq;
			} else if (event.getEventType().getName().equals("app.bufEnqOp")) {
				v[i++] = enq;
			} else if (event.getEventType().getName().equals("app.bufWaitOp")) {
				if ("p".equals(event.getString("type"))) {
					v[i++] = waitP;
				} else {
					v[i++] = waitC;
				}
			}
		}

		final ValueOutputStream vos = new ValueOutputStream(out.toFile(), true);
		// Do not normalize TupleValue because normalization depends on the actual
		// UniqueString#internTable.
		new TupleValue(v).write(vos);
		vos.close();

		System.out.printf("Successfully serialized to %s.\n", out);
	}
}

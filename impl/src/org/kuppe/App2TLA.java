package org.kuppe;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.List;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;
import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;

public class App2TLA {

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

		printTrace(recordedEvents);
	}

	private static void printTrace(final List<RecordedEvent> events) {
		// Format each step in the execution as a TLA+ record.
		for (RecordedEvent event : events) {
			if (event.getEventType().getName().equals("app.bufDeqOp")) {
				System.out.printf("[ op |-> \"d\" ],\n");
			} else if (event.getEventType().getName().equals("app.bufEnqOp")) {
				System.out.printf("[ op |-> \"e\" ],\n");
			} else if (event.getEventType().getName().equals("app.bufWaitOp")) {
				System.out.printf("[ op |-> \"w\", waiter |-> \"%s\" ],\n", event.getString("type"));
			}
		}
	}
}

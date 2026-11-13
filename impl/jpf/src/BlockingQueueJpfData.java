import java.io.BufferedReader;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * Row n describes node n (node zero is the empty history).  Queue transitions
 * and acceptance belong to the TLA+ adapter, not this loader.
 */
public final class BlockingQueueJpfData {
    private static final List<RecordValue> EVENTS = new ArrayList<>();
    private static final List<SetEnumValue> CHILDREN = new ArrayList<>();

    static {
        Path path = Path.of(System.getProperty("blockingqueue.jpf.nodes", "build/jpf/nodes.tsv"));
        EVENTS.add(null);
        List<List<Value>> children = new ArrayList<>();
        children.add(new ArrayList<>());
        Set<String> edges = new HashSet<>();
        try (BufferedReader input = Files.newBufferedReader(path)) {
            if (!"parent\tthread\taction".equals(input.readLine())) {
                throw malformed(path, 1, "expected parent, thread, action TSV header");
            }
            for (String line; (line = input.readLine()) != null;) {
                int node = EVENTS.size();
                String[] row = line.split("\t", -1);
                if (row.length != 3 || row[1].isEmpty() || row[2].isEmpty()) {
                    throw malformed(path, node + 1, "expected three nonempty TSV fields");
                }
                final int parent;
                try {
                    parent = Integer.parseInt(row[0]);
                } catch (NumberFormatException e) {
                    throw malformed(path, node + 1, "parent is not an integer");
                }
                if (parent < 0 || parent >= node) {
                    throw malformed(path, node + 1, "parent must precede its child");
                }
                if (!edges.add(parent + "\t" + row[1] + "\t" + row[2])) {
                    throw malformed(path, node + 1, "duplicate outgoing event");
                }
                children.get(parent).add(IntValue.gen(node));
                EVENTS.add(new RecordValue(
                        new UniqueString[] { UniqueString.of("thread"), UniqueString.of("action") },
                        new Value[] { new StringValue(row[1]), new StringValue(row[2]) }, false));
                children.add(new ArrayList<>());
            }
        } catch (IOException e) {
            throw new UncheckedIOException("Cannot read JPF prefix tree " + path, e);
        }
        if (EVENTS.size() == 1) {
            throw malformed(path, 2, "empty observation tree");
        }
        children.forEach(c -> CHILDREN.add(new SetEnumValue(c.toArray(new Value[0]), false)));
    }

    private BlockingQueueJpfData() { }

    private static IllegalArgumentException malformed(Path path, int line, String message) {
        return new IllegalArgumentException(path + ":" + line + ": " + message);
    }

    public static Value JpfNodeCount() {
        return IntValue.gen(EVENTS.size() - 1);
    }

    public static Value JpfChildren(Value node) {
        return CHILDREN.get(nodeNumber(node, true));
    }

    public static Value JpfEvent(Value node) {
        return EVENTS.get(nodeNumber(node, false));
    }

    private static int nodeNumber(Value node, boolean rootAllowed) {
        if (!(node instanceof IntValue)) {
            throw new IllegalArgumentException("JPF node must be an integer: " + node);
        }
        int n = ((IntValue) node).val;
        if (n < (rootAllowed ? 0 : 1) || n >= EVENTS.size()) {
            throw new IllegalArgumentException("JPF node out of range: " + n);
        }
        return n;
    }
}

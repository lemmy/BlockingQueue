package org.kuppe.jpf;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.fasterxml.jackson.dataformat.cbor.CBORFactory;
import com.fasterxml.jackson.dataformat.cbor.CBORGenerator;

import gov.nasa.jpf.ListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * Collects the observation prefixes encountered during a JPF depth-first search.
 * A subclass decides what to observe and calls {@link #record(ThreadInfo, String)}
 * for each event. This class handles the search history and its export; the
 * meaning of the events and their agreement with a specification belong to the
 * observer and the later trace-validation step.
 *
 * <p>JPF explores a path, backtracks, and explores another scheduling choice.
 * Observations made after backtracking belong to an alternative execution.
 * For example, paths observing A, B and A, C form a tree with a shared prefix A
 * and two children B and C. A chronological callback log would concatenate
 * these alternatives into a sequence that the program never executed.
 *
 * <p>The tree lives in the host JVM, outside the program state that JPF explores.
 * Recording an event therefore leaves JPF's state matching unchanged, and JPF
 * backtracking does not erase previously collected branches. Each tree node
 * identifies an observation prefix: equal events following the same parent
 * share a node. Different histories can lead to the same Java program state
 * and still have distinct tree nodes; different program states can also share
 * the same observation prefix.
 *
 * <p>{@code current} follows the observations along the active search path.
 * At each DFS depth, {@code prefixesByDepth} checkpoints this cursor. A JPF
 * transition can contain several observations, or none. Backtracking restores
 * the cursor to the checkpoint at the restored depth and discards deeper
 * checkpoints. The accumulated tree survives, ready to receive another branch
 * from that prefix. This relies on DFS backtracking rather than arbitrary state
 * restoration.
 *
 * <p>Every node represents a prefix worth retaining, including a leaf where
 * JPF encounters an already visited program state and stops extending that
 * path. Such a leaf can end inside a call; it need not be a completed execution.
 * The recorder does not extend it with continuations from a different history.
 * State matching and scheduling reductions still determine which paths JPF
 * explores. Keeping the observation tree outside JPF does not disable them.
 *
 * <p>When the search finishes, export one CBOR array of records with fields
 * {@code parent}, {@code thread}, and {@code action}. Node zero is the empty
 * history; array element n (counting from one) defines node n. Following parent
 * links reconstructs that node's observation sequence. Jackson writes the array
 * and records with explicit lengths so TLC's CBOR module can read them directly.
 * Errors or reported search constraints delete the output and raise an
 * exception instead. Validation of the recorded prefixes belongs to TLC.
 */
public abstract class TraceRecorder extends ListenerAdapter {
    private static final class Node {
        final int parent;
        final String thread;
        final String action;

        Node(int parent, String thread, String action) {
            this.parent = parent;
            this.thread = thread;
            this.action = action;
        }
    }

    private final Path output = Path.of(System.getProperty("blockingqueue.jpf.nodes", "nodes.cbor"));
    // The tree accumulates across the entire search, including backtracked paths.
    private final Map<List<Object>, Integer> edges = new HashMap<>();
    private final List<Node> nodes = new ArrayList<>();
    // Only the active path's cursor needs to move backward with JPF.
    private final List<Integer> prefixesByDepth = new ArrayList<>(List.of(0));
    private int current;

    protected final void record(ThreadInfo thread, String action) {
        record(thread.getName(), action);
    }

    /** Extends the current prefix by one event, reusing an existing child if any. */
    protected final void record(String thread, String action) {
        List<Object> edge = List.of(current, thread, action);
        Integer child = edges.get(edge);
        if (child == null) {
            child = nodes.size() + 1;
            nodes.add(new Node(current, thread, action));
            edges.put(edge, child);
        }
        current = child;
    }

    @Override
    public void stateAdvanced(Search search) {
        prefixesByDepth.add(current);
    }

    @Override
    public void stateBacktracked(Search search) {
        int depth = search.getDepth();
        prefixesByDepth.subList(depth + 1, prefixesByDepth.size()).clear();
        current = prefixesByDepth.get(depth);
    }

    @Override
    public void searchFinished(Search search) {
        if (search.hasErrors() || search.getLastSearchConstraint() != null) {
            try {
                Files.deleteIfExists(output);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
            throw new IllegalStateException("JPF found errors or hit a search constraint; no trace exported");
        }
        try (CBORGenerator cbor = new CBORFactory().createGenerator(Files.newOutputStream(output))) {
            cbor.writeStartArray(null, nodes.size());
            for (Node node : nodes) {
                cbor.writeStartObject(null, 3);
                cbor.writeNumberField("parent", node.parent);
                cbor.writeStringField("thread", node.thread);
                cbor.writeStringField("action", node.action);
                cbor.writeEndObject();
            }
            cbor.writeEndArray();
            System.out.println("Recorded " + nodes.size() + " BlockingQueue execution prefixes.");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}

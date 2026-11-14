package org.kuppe.jpf;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import gov.nasa.jpf.ListenerAdapter;
import gov.nasa.jpf.search.DFSearch;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * History stays outside JPF state matching; only its cursor is restored on DFS
 * backtracking. Subclasses select observations without modifying Java state.
 */
public abstract class TraceRecorder extends ListenerAdapter {
    private final Path output = Path.of(System.getProperty("blockingqueue.jpf.nodes", "nodes.tsv"));
    private final Map<String, Integer> edges = new HashMap<>();
    private final List<String> nodes = new ArrayList<>(List.of("parent\tthread\taction"));
    private final List<Integer> prefixesByDepth = new ArrayList<>(List.of(0));
    private int current;
    private boolean limited;

    protected final void record(ThreadInfo thread, String action) {
        record(thread.getName(), action);
    }

    protected final void record(String thread, String action) {
        checkField(thread);
        checkField(action);
        String edge = current + "\t" + thread + "\t" + action;
        Integer child = edges.get(edge);
        if (child == null) {
            child = nodes.size();
            nodes.add(edge);
            edges.put(edge, child);
        }
        current = child;
    }

    private static void checkField(String field) {
        if (field == null || field.isEmpty() || field.indexOf('\t') >= 0
                || field.indexOf('\n') >= 0 || field.indexOf('\r') >= 0) {
            throw new IllegalArgumentException("Invalid JPF observation field: " + field);
        }
    }

    @Override
    public void searchStarted(Search search) {
        // A failed collection must never leave a previous successful export.
        try {
            Files.deleteIfExists(output);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (!(search instanceof DFSearch)) {
            throw new IllegalStateException("Use DFSearch for BlockingQueue trace collection");
        }
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
    public void stateRestored(Search search) {
        throw new IllegalStateException("State restoration is unsupported; use DFSearch");
    }

    @Override
    public void searchConstraintHit(Search search) {
        limited = true;
    }

    @Override
    public void searchFinished(Search search) {
        if (limited || search.isDone() || search.getDepth() != 0 || !search.getErrors().isEmpty()) {
            throw new IllegalStateException("JPF search did not finish successfully; no trace exported");
        }
        if (nodes.size() == 1) {
            throw new IllegalStateException("JPF produced no BlockingQueue observations");
        }
        try {
            Files.write(output, nodes);
            System.out.println("Recorded " + (nodes.size() - 1) + " BlockingQueue execution prefixes.");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}

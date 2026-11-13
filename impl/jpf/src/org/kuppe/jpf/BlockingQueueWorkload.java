package org.kuppe.jpf;

import org.kuppe.BlockingQueue;

/** A finite, balanced p2c2b1 workload; use the real queue, without App's sleeps. */
public final class BlockingQueueWorkload {
    private static final class Worker extends Thread {
        private final BlockingQueue<String> queue;
        private final boolean producer;

        Worker(String name, BlockingQueue<String> queue, boolean producer) {
            super(name);
            this.queue = queue;
            this.producer = producer;
        }

        @Override
        public void run() {
            try {
                if (producer) {
                    queue.put(getName());
                } else {
                    String value = queue.take();
                    assert value != null;
                }
            } catch (InterruptedException e) {
                throw new AssertionError(e);
            }
        }
    }

    public static void main(String[] args) throws InterruptedException {
        BlockingQueue<String> queue = new BlockingQueue<>(1);
        Thread[] workers = {
            new Worker("p1", queue, true), new Worker("p2", queue, true),
            new Worker("c1", queue, false), new Worker("c2", queue, false)
        };
        for (Thread worker : workers) {
            worker.start();
        }
        for (Thread worker : workers) {
            worker.join();
        }
    }
}

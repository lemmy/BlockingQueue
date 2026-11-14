package org.kuppe.jpf;

import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/** Observes public queue calls and returns without changing JPF's heap. */
public class BlockingQueueListener extends TraceRecorder {
    protected static final String QUEUE = "org.kuppe.BlockingQueue.";
    private static final String PUT = QUEUE + "put(Ljava/lang/Object;)V";
    private static final String TAKE = QUEUE + "take()Ljava/lang/Object;";

    @Override
    public void methodEntered(VM vm, ThreadInfo thread, MethodInfo method) {
        String name = method.getFullName();
        if (name.equals(PUT)) {
            record(thread, "put.call." + stringValue(thread, thread.getTopFrame().getLocalVariable(1)));
        } else if (name.equals(TAKE)) {
            record(thread, "take.call");
        }
    }

    @Override
    public void methodExited(VM vm, ThreadInfo thread, MethodInfo method) {
        String name = method.getFullName();
        // Only normal returns are responses; JPF checks uncaught exceptions.
        if (!(thread.getPC() instanceof JVMReturnInstruction)) {
            return;
        }
        // The callee's frame and actual return operand are still present.
        // Method callbacks avoid duplicate events from scheduling reexecution.
        if (name.equals(PUT)) {
            record(thread, "put.return");
        } else if (name.equals(TAKE)) {
            record(thread, "take.return." + stringValue(thread, thread.getTopFrame().peek()));
        }
    }

    protected final String stringValue(ThreadInfo thread, int reference) {
        ElementInfo value = thread.getElementInfo(reference);
        // A Java null has no ElementInfo (a defect here, or put(null) in another
        // workload). Record it rather than crashing the listener.
        return value == null ? "null" : value.asString();
    }
}

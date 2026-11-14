package org.kuppe.jpf;

import gov.nasa.jpf.jvm.bytecode.JVMReturnInstruction;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/** Observes the implementation without adding trace state to JPF's heap. */
public final class BlockingQueueListener extends TraceRecorder {
    private static final String QUEUE = "org.kuppe.BlockingQueue.";
    private static final String AWAIT = "java.util.concurrent.locks.AbstractQueuedSynchronizer$ConditionObject.await()V";

    private boolean queueCall(ThreadInfo thread) {
        for (StackFrame frame : thread) {
            String name = frame.getMethodInfo().getFullName();
            if (name.equals(QUEUE + "put(Ljava/lang/Object;)V")
                    || name.equals(QUEUE + "take()Ljava/lang/Object;")) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void methodEntered(VM vm, ThreadInfo thread, MethodInfo method) {
        if (method.getFullName().equals(AWAIT) && queueCall(thread)) {
            record(thread, "wait");
        }
    }

    @Override
    public void methodExited(VM vm, ThreadInfo thread, MethodInfo method) {
        String name = method.getFullName();
        boolean append = name.equals(QUEUE + "append(Ljava/lang/Object;)V");
        boolean head = name.equals(QUEUE + "head()Ljava/lang/Object;");
        boolean await = name.equals(AWAIT) && queueCall(thread);
        if (!append && !head && !await) {
            return;
        }
        // Called while the callee's frame (and return operand) is still present.
        // Method callbacks avoid duplicate events from scheduling reexecution.
        if (!(thread.getPC() instanceof JVMReturnInstruction)) {
            throw new IllegalStateException("Observed exceptional return: " + name);
        }
        if (head) {
            ElementInfo value = thread.getElementInfo(thread.getTopFrame().peek());
            record(thread, "take." + (value == null ? "null" : value.asString()));
        } else {
            record(thread, append ? "put" : "resume");
        }
    }
}

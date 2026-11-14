----------------------- MODULE BlockingQueueJpfTrace ------------------------
EXTENDS BlockingQueueSplit, BlockingQueueJpfData, TLC

\* Reuse the queue actions; the Java overrides supply observations only.
\* Reject missing overrides or an empty collection instead of accepting it.
ASSUME JpfNodeCount > 0

\* Coverage uses worker-local registers and requires exhaustive exploration.
ASSUME TLCGet("config").worker = 1
ASSUME TLCGet("config").mode = "bfs"
\* Finite recorded prefixes can end without an enabled successor.
ASSUME TLCGet("config").deadlock = FALSE

VARIABLE node

TraceInit ==
    /\ Init
    /\ node = 0
    /\ TLCSet(0, {0})

TraceTypeInv == node \in 0..JpfNodeCount

Observe(t, a) ==
    \/ /\ t \in Producers
       /\ a = "put"
       /\ Len(buffer) < BufCapacity
       /\ Put(t, t)
    \/ /\ t \in Consumers
       /\ buffer # <<>>
       /\ a = "take." \o Head(buffer)
       /\ Get(t)
    \/ /\ a = "wait"
       /\ \/ /\ t \in Producers
             /\ Len(buffer) = BufCapacity
             /\ Put(t, t)
          \/ /\ t \in Consumers
             /\ buffer = <<>>
             /\ Get(t)
    \/ /\ a = "resume"
       /\ t \in RunningThreads
       /\ UNCHANGED vars

\* Put/Get include the abstract notification. Java signals immediately before
\* append/head under the same lock, so no other queue observation can intervene.
\* The signaled thread remains an existential choice, constrained by later
\* resumes. This workload does not explore interrupts or spurious wakeups.
TraceStep(child) ==
    /\ LET event == JpfEvent(child)
       IN Observe(event.thread, event.action)
    /\ node' = child

\* Each step consumes exactly one observation; no unobserved queue operations.
TraceNext == \E child \in JpfChildren(node): TraceStep(child)

\* An impossible observation disables its branch. Merely reaching one leaf
\* therefore proves nothing about its siblings: every recorded prefix must
\* have some matching specification prefix, including JPF state-match leaves.
\* Accumulate visited nodes outside state fingerprints in worker-local registers.
RememberNodes == TLCSet(0, TLCGet(0) \cup {node})
AllNodesReplayed == TLCGet(0) = 0..JpfNodeCount
=============================================================================

----------------------- MODULE BlockingQueueJpfTrace ------------------------
EXTENDS BlockingQueueSplit, CBOR, TLC

CONSTANTS TraceFile, Data

\* Each array element is [parent |-> ..., thread |-> ..., action |-> ...].
\* Element n describes node n; node zero is the empty history.
\* These constant definitions are evaluated once, outside the replay states.
Nodes == CBORDeserialize(TraceFile)
JpfNodeCount == Len(Nodes)

Children == [n \in 0..JpfNodeCount |->
                {child \in 1..JpfNodeCount : Nodes[child].parent = n}]
JpfChildren(n) == Children[n]
JpfEvent(n) == Nodes[n]

\* Reject an empty collection.
ASSUME JpfNodeCount > 0
\* Indexed coverage registers belong to individual workers.
ASSUME TLCGet("config").worker = 1
ASSUME TLCGet("config").mode = "bfs"
\* Finite recorded prefixes can end inside an unfinished call.
ASSUME TLCGet("config").deadlock = FALSE

VARIABLES node, pending

CallEvents == {"take.call"} \cup {"put.call." \o d : d \in Data}
ReturnEvents == {"put.return"} \cup {"take.return." \o d : d \in Data}

TraceInit ==
    /\ Init
    /\ node = 0
    /\ pending = [t \in Producers \cup Consumers |-> ""]
    /\ TLCSet(0, {0})

TraceTypeInv ==
    /\ node \in 0..JpfNodeCount
    /\ pending \in [Producers \cup Consumers -> {""} \cup CallEvents \cup ReturnEvents]

\* Invocation and response events leave the abstract queue unchanged.
\* The actual put argument and take result are retained in the event labels.
PublicEvent(t, a) ==
    /\ \/ /\ t \in Producers
          /\ a \in {"put.call." \o d : d \in Data}
          /\ pending[t] = ""
          /\ pending' = [pending EXCEPT ![t] = a]
       \/ /\ t \in Consumers
          /\ a = "take.call"
          /\ pending[t] = ""
          /\ pending' = [pending EXCEPT ![t] = a]
       \/ /\ t \in Producers \cup Consumers
          /\ a \in ReturnEvents
          /\ a = pending[t]
          /\ pending' = [pending EXCEPT ![t] = ""]
    /\ UNCHANGED vars

\* Successful Put/Get steps occur at append/head observations, before the
\* matching public response.
LinearizePut(t, value) ==
    /\ t \in Producers
    /\ value \in Data
    /\ pending[t] = "put.call." \o value
    /\ Len(buffer) < BufCapacity
    /\ Put(t, value)
    /\ pending' = [pending EXCEPT ![t] = "put.return"]

LinearizeTake(t) ==
    /\ t \in Consumers
    /\ pending[t] = "take.call"
    /\ buffer # <<>>
    /\ Get(t)
    /\ pending' = [pending EXCEPT ![t] = "take.return." \o Head(buffer)]

TraceStep(child) ==
    /\ LET event == JpfEvent(child)
           t == event.thread
           a == event.action
       IN \/ PublicEvent(t, a)
          \/ \E d \in Data :
                 /\ a = "append." \o d
                 /\ LinearizePut(t, d)
          \/ /\ t \in Consumers
             /\ buffer # <<>>
             /\ a = "head." \o Head(buffer)
             /\ LinearizeTake(t)
          \/ /\ a = "wait"
             /\ \/ /\ t \in Producers
                   /\ Len(buffer) = BufCapacity
                   /\ \E d \in Data :
                          /\ pending[t] = "put.call." \o d
                          /\ Put(t, d)
                \/ /\ t \in Consumers
                   /\ pending[t] = "take.call"
                   /\ buffer = <<>>
                   /\ Get(t)
             /\ UNCHANGED pending
          \/ /\ a = "resume"
             /\ t \in RunningThreads
             /\ pending[t] \in CallEvents
             /\ UNCHANGED <<vars, pending>>
    /\ node' = child

\* Every step consumes an observation; no hidden queue step can justify a
\* response without its matching append/head event.
TraceNext == \E child \in JpfChildren(node): TraceStep(child)

\* Every recorded prefix needs some matching abstract execution. An impossible
\* response otherwise just disables its branch when deadlock checking is off.
\* Matched-state leaves may end with an invocation or response still pending.
RememberNodes == TLCSet(0, TLCGet(0) \cup {node})
AllNodesReplayed == TLCGet(0) = 0..JpfNodeCount
=============================================================================

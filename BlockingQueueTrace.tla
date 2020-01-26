------------------------- MODULE BlockingQueueTrace -------------------------
EXTENDS TLC, Sequences, Naturals, FiniteSets

(* Matches the configuration of the app. *)
Producers == {"p1","p2","p3","p4"}
Consumers == {"c1","c2","c3"}
BufCapacity == 3

(* Copy&Pasted from stdout. *)
TraceShort == <<
[ op |-> "w", waiter |-> "c" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "w", waiter |-> "c" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "w", waiter |-> "c" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "w", waiter |-> "c" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "w", waiter |-> "p" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "w", waiter |-> "c" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "d" ],
[ op |-> "e" ],
[ op |-> "d" ],
[ op |-> "e" ]
>>

Trace == TraceShort

-----------------------------------------------------------------------------

kSubsets(S, k) == IF S = {}
                  THEN {{}} \* kSubset of the empty set is the empty set.
                  ELSE { s \in SUBSET S : Cardinality(s) = k}

VARIABLES buffer, waitSet, i
vars == <<buffer, waitSet, i>>

Init == /\ i = 1
        /\ waitSet = {}
        /\ buffer = <<>>

waitP == /\ i <= Len(Trace)
         /\ i' = i + 1
         /\ Trace[i].op = "w"
         /\ Trace[i].waiter = "p"
         (* The trace is incomplete because the App does not log the actual thread  *)
         (* that waits (the log only contains weather it is a consumer or producer).*)
         (* Thus, we select a running producer and add it to waitSet.               *)
         /\ waitSet' \in { waitSet \cup {t} : t \in (Producers \ waitSet) }
         /\ UNCHANGED buffer

waitC == /\ i <= Len(Trace)
         /\ i' = i + 1
         /\ Trace[i].op = "w"
         /\ Trace[i].waiter = "c"
         /\ waitSet' \in { waitSet \cup {t} : t \in (Consumers \ waitSet) }
         /\ UNCHANGED buffer

put == /\ i <= Len(Trace)
       /\ i' = i + 1
       /\ Trace[i].op = "e"
       (* The trace is incomplete because the App does not log which thread gets *)
       (* notified. Thus, we here notify a thread non-deterministically (the     *)
       (* same happens below in get).                                            *)
       /\ waitSet' \in kSubsets(waitSet, Cardinality(waitSet) - 1)
       (* The trace is also incomplete with regards to the buffer. Thus, we non- *)
       (* deterministically append an element to the buffer (again same below).  *)
       (* Note that only non-waiting producers can append.                       *)
       /\ buffer' \in { Append(buffer, e) : e \in (Producers \ waitSet) }
       
get == /\ i <= Len(Trace)
       /\ i' = i + 1
       /\ Trace[i].op = "d"
       /\ waitSet' \in kSubsets(waitSet, Cardinality(waitSet) - 1)
       /\ buffer # <<>>
       /\ buffer' = Tail(buffer)
       
(* Infinite stuttering... *)
term == /\ i > Len(Trace)
        /\ UNCHANGED vars
               
Next == \/ waitP
        \/ waitC
        \/ put
        \/ get
        \/ term          

-----------------------------------------------------------------------------

TraceBehavior == Init /\ [][Next]_vars /\ WF_vars(Next)

Complete == <>[](i = Len(Trace) + 1)

BQ == INSTANCE BlockingQueue

THEOREM TraceBehavior => BQ!Invariant

BQInv == BQ!Invariant
BQSpec == BQ!Spec
=============================================================================

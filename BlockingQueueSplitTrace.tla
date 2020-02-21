$ cd impl && make clean ; make trace && cd ..
$ impl/producer_consumer 3 4 3 > impl/out.csv
$ tlc -note -config BlockingQueueTrace.cfg BlockingQueueSplitTrace.tla

----------------------- MODULE BlockingQueueSplitTrace -----------------------
EXTENDS TLC, Sequences, Naturals, FiniteSets, CSV

(* Matches the configuration of the app. *)
Producers == {"p1","p2","p3","p4"}
Consumers == {"c1","c2","c3"}
BufCapacity == 3

\* Read the first two columns from the CSV file impl/out.csv into
\* a sequence of records.  The first column of the CSV file is the
\* operation ((e)nqueue, (w)ait, (d)equeue).  The second column
\* indicates if a (c)onsumer or (p)roducer is executing.
\* For completeness, the third column is the consumer thread's id,
\* iff the second column is 'c', and -1 otherwise (the implementation
\* does not log the producer identifiers).
\*
\* $ head -8 impl/out.csv 
\* e#p#-1
\* e#p#-1
\* e#p#-1
\* w#p#-1
\* d#c#0
\* d#c#0
\* d#c#1
\* w#c#1
\*
\* CSVRead is nested inside TLCEval to force TLC to read the file
\* only once and not on each evaluation of the definition of Trace.
Trace == TLCEval(CSVRead(<<"op", "waiter">>, "#", "impl/out.csv"))
-----------------------------------------------------------------------------

kSubsets(S, k) == IF S = {}
                  THEN {{}} \* kSubset of the empty set is the empty set.
                  ELSE { s \in SUBSET S : Cardinality(s) = k}

VARIABLES buffer, waitSetC, waitSetP, i
vars == <<buffer, waitSetC, waitSetP, i>>

Init == /\ i = 1
        /\ waitSetC = {}
        /\ waitSetP = {}
        /\ buffer = <<>>

waitP == /\ i <= Len(Trace)
         /\ i' = i + 1
         /\ Trace[i].op = "w"
         /\ Trace[i].waiter = "p"
         (* The trace is incomplete because the App does not log the actual thread  *)
         (* that waits (the log only contains weather it is a consumer or producer).*)
         (* Thus, we select a running producer and add it to waitSet.               *)
         /\ waitSetP' \in { waitSetP \cup {t} : t \in (Producers \ waitSetP) }
         /\ UNCHANGED <<buffer, waitSetC>>

waitC == /\ i <= Len(Trace)
         /\ i' = i + 1
         /\ Trace[i].op = "w"
         /\ Trace[i].waiter = "c"
         /\ waitSetC' \in { waitSetC \cup {t} : t \in (Consumers \ waitSetC) }
         /\ UNCHANGED <<buffer, waitSetP>>

put == /\ i <= Len(Trace)
       /\ i' = i + 1
       /\ Trace[i].op = "e"
       (* The trace is incomplete because the App does not log which thread gets *)
       (* notified. Thus, we here notify a thread non-deterministically (the     *)
       (* same happens below in get).                                            *)
       /\ waitSetC' \in kSubsets(waitSetC, Cardinality(waitSetC) - 1)
       (* The trace is also incomplete with regards to the buffer. Thus, we non- *)
       (* deterministically append an element to the buffer (again same below).  *)
       (* Note that only non-waiting producers can append.                       *)
       /\ buffer' \in { Append(buffer, e) : e \in (Producers \ waitSetP) }
       /\ UNCHANGED waitSetP
       
get == /\ i <= Len(Trace)
       /\ i' = i + 1
       /\ Trace[i].op = "d"
       /\ waitSetP' \in kSubsets(waitSetP, Cardinality(waitSetP) - 1)
       /\ buffer # <<>>
       /\ buffer' = Tail(buffer)
       /\ UNCHANGED waitSetC
       
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

BQ == INSTANCE BlockingQueueSplit

THEOREM TraceBehavior => BQ!A!Invariant

BQInv == BQ!A!Invariant
BQSpec == BQ!Spec
=============================================================================

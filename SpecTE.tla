@!@!@STARTMSG 1000:0 @!@!@
Will generate a SpecTE file pair if error states are encountered.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2262:0 @!@!@
TLC2 Version 2.15 of Day Month 20?? (rev: 2a12f60)
@!@!@ENDMSG 2262 @!@!@
@!@!@STARTMSG 2187:0 @!@!@
Running breadth-first search Model-Checking with fp 21 and seed 647230902156660305 with 1 worker on 4 cores with 5301MB heap and 64MB offheap memory (Linux 4.18.0-16-generic amd64, Oracle Corporation 1.8.0_201 x86_64, MSBDiskFPSet, DiskStateQueue).
@!@!@ENDMSG 2187 @!@!@
@!@!@STARTMSG 2220:0 @!@!@
Starting SANY...
@!@!@ENDMSG 2220 @!@!@
Parsing file /home/markus/src/TLA/_specs/models/tutorials/BlockingQueueTLA/BlockingQueue.tla
Parsing file /tmp/Naturals.tla
Parsing file /tmp/Sequences.tla
Parsing file /tmp/FiniteSets.tla
Parsing file /tmp/TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module BlockingQueue
@!@!@STARTMSG 2219:0 @!@!@
SANY finished.
@!@!@ENDMSG 2219 @!@!@
@!@!@STARTMSG 2185:0 @!@!@
Starting... (2020-01-16 22:25:03)
@!@!@ENDMSG 2185 @!@!@
@!@!@STARTMSG 2189:0 @!@!@
Computing initial states...
@!@!@ENDMSG 2189 @!@!@
@!@!@STARTMSG 2269:0 @!@!@
Computed 2 initial states...
@!@!@ENDMSG 2269 @!@!@
@!@!@STARTMSG 2190:0 @!@!@
Finished computing initial states: 3 distinct states generated at 2020-01-16 22:25:03.
@!@!@ENDMSG 2190 @!@!@
@!@!@STARTMSG 2110:1 @!@!@
Invariant Invariant is violated.
@!@!@ENDMSG 2110 @!@!@
@!@!@STARTMSG 2121:1 @!@!@
The behavior up to this point is:
@!@!@ENDMSG 2121 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
1: <Initial predicate>
/\ buffer = <<>>
/\ waitSet = {}
/\ thread = p1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
2: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<F>>
/\ waitSet = {}
/\ thread = p1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
3: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<F>>
/\ waitSet = {p1}
/\ thread = p2

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
4: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<F>>
/\ waitSet = {p1, p2}
/\ thread = c1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
5: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<>>
/\ waitSet = {p2}
/\ thread = c1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
6: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<>>
/\ waitSet = {p2, c1}
/\ thread = p1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
7: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<N>>
/\ waitSet = {c1}
/\ thread = p1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
8: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<N>>
/\ waitSet = {p1, c1}
/\ thread = p2

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
9: <Next line 58, col 12 to line 63, col 31 of module BlockingQueue>
/\ buffer = <<N>>
/\ waitSet = {p1, p2, c1}
/\ thread = p1

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2200:0 @!@!@
Progress(9) at 2020-01-16 22:25:03: 235 states generated (28,200 s/min), 106 distinct states found (12,720 ds/min), 13 states left on queue.
@!@!@ENDMSG 2200 @!@!@
@!@!@STARTMSG 2199:0 @!@!@
235 states generated, 106 distinct states found, 13 states left on queue.
@!@!@ENDMSG 2199 @!@!@
@!@!@STARTMSG 2194:0 @!@!@
The depth of the complete state graph search is 9.
@!@!@ENDMSG 2194 @!@!@
@!@!@STARTMSG 2268:0 @!@!@
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 6 and the 95th percentile is 3).
@!@!@ENDMSG 2268 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The model check run produced error-states - we will generate the SpecTE files now.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The file /home/markus/src/TLA/_specs/models/tutorials/BlockingQueueTLA/SpecTE.tla has been created.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The file /home/markus/src/TLA/_specs/models/tutorials/BlockingQueueTLA/SpecTE.cfg has been created.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2186:0 @!@!@
Finished in 542ms at (2020-01-16 22:25:03)
@!@!@ENDMSG 2186 @!@!@
--------------------------- MODULE SpecTE ----
EXTENDS Sequences, Toolbox, TLC, Naturals, FiniteSets

\* 
\*  SpecTE follows
\* 


CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity, (* the maximum number of messages in the bounded buffer  *)
          Data

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet, thread
vars == <<buffer, waitSet, thread>>

RunningThreads == (Producers \cup Consumers) \ waitSet

(* @see java.lang.Object#notify *)       
Notify == IF waitSet # {}
          THEN \E x \in waitSet: waitSet' = waitSet \ {x}
          ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
   \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ Notify
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
   \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ Notify
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}
        /\ thread \in (Producers \cup Consumers)

(* Then, pick a thread out of all running threads and have it do its thing. *)
\* Next rewritten to predict the value of a prophecy variable
\* http://lamport.azurewebsites.net/pubs/auxiliary.pdf
\* (https://github.com/lorin/tla-prophecy)
Next == \/ /\ thread \notin waitSet                        \* Pred_A(i)
           /\ thread' \in (Producers \cup Consumers)       \* Setp
           /\ \/ /\ thread \in Producers                   \* A
                 /\ Put(thread, RandomElement(Data)) \* Add some data to buffer
              \/ /\ thread \in Consumers
                 /\ Get(thread)
        \/ /\ thread \in waitSet
           /\ UNCHANGED vars

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\ buffer \in Seq(Data)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \subseteq (Producers \cup Consumers)

(* No Deadlock *)
Invariant == waitSet # (Producers \cup Consumers)


CONSTANTS p1, A, p2, B, C, D, E, F, G, H, I, J, K, L, M, c1, N, O, P, Q, R, S, T

\* TRACE Sub-Action definition 0
Next_sa_0 ==
    (
        /\ buffer = (<<>>)
        /\ waitSet = ({})
        /\ thread = (p1)
        /\ buffer' = (<<F>>)
        /\ waitSet' = ({})
        /\ thread' = (p1)
    )

\* TRACE Sub-Action definition 1
Next_sa_1 ==
    (
        /\ buffer = (<<F>>)
        /\ waitSet = ({})
        /\ thread = (p1)
        /\ buffer' = (<<F>>)
        /\ waitSet' = ({p1})
        /\ thread' = (p2)
    )

\* TRACE Sub-Action definition 2
Next_sa_2 ==
    (
        /\ buffer = (<<F>>)
        /\ waitSet = ({p1})
        /\ thread = (p2)
        /\ buffer' = (<<F>>)
        /\ waitSet' = ({p1, p2})
        /\ thread' = (c1)
    )

\* TRACE Sub-Action definition 3
Next_sa_3 ==
    (
        /\ buffer = (<<F>>)
        /\ waitSet = ({p1, p2})
        /\ thread = (c1)
        /\ buffer' = (<<>>)
        /\ waitSet' = ({p2})
        /\ thread' = (c1)
    )

\* TRACE Sub-Action definition 4
Next_sa_4 ==
    (
        /\ buffer = (<<>>)
        /\ waitSet = ({p2})
        /\ thread = (c1)
        /\ buffer' = (<<>>)
        /\ waitSet' = ({p2, c1})
        /\ thread' = (p1)
    )

\* TRACE Sub-Action definition 5
Next_sa_5 ==
    (
        /\ buffer = (<<>>)
        /\ waitSet = ({p2, c1})
        /\ thread = (p1)
        /\ buffer' = (<<N>>)
        /\ waitSet' = ({c1})
        /\ thread' = (p1)
    )

\* TRACE Sub-Action definition 6
Next_sa_6 ==
    (
        /\ buffer = (<<N>>)
        /\ waitSet = ({c1})
        /\ thread = (p1)
        /\ buffer' = (<<N>>)
        /\ waitSet' = ({p1, c1})
        /\ thread' = (p2)
    )

\* TRACE Action Constraint definition traceExploreActionConstraint
_SpecTEActionConstraint ==
<<
Next_sa_0,
Next_sa_1,
Next_sa_2,
Next_sa_3,
Next_sa_4,
Next_sa_5,
Next_sa_6
>>[TLCGet("level")]
----

def_ov_15792423033492000 == 
<<
([buffer |-> <<>>,waitSet |-> {},thread |-> p1]),
([buffer |-> <<F>>,waitSet |-> {},thread |-> p1]),
([buffer |-> <<F>>,waitSet |-> {p1},thread |-> p2]),
([buffer |-> <<F>>,waitSet |-> {p1, p2},thread |-> c1]),
([buffer |-> <<>>,waitSet |-> {p2},thread |-> c1]),
([buffer |-> <<>>,waitSet |-> {p2, c1},thread |-> p1]),
([buffer |-> <<N>>,waitSet |-> {c1},thread |-> p1]),
([buffer |-> <<N>>,waitSet |-> {p1, c1},thread |-> p2])
>>
----

INSTANCE BlockingQueueAnim

VARIABLE TraceExp

\* TRACE INIT definition traceExploreInit
_SpecTEInit ==
    /\ buffer = (
            <<>>
        )
    /\ waitSet = (
            {}
        )
    /\ thread = (
            p1
        )
    /\ TraceExp = Animation

----

\* TRACE NEXT definition traceExploreNext
_SpecTENext ==
/\  \/ Next_sa_0
    \/ Next_sa_1
    \/ Next_sa_2
    \/ Next_sa_3
    \/ Next_sa_4
    \/ Next_sa_5
    \/ Next_sa_6
 /\ TraceExp' = Animation



=============================================================================

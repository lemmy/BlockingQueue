----------------------- MODULE BlockingQueuePoisonPill -----------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
-----------------------------------------------------------------------------
\* These three variables are pratically constants but have to be VARIABLES because TLC
\* doesn't support verification of sets of CONSTANT values.
\* (see https://github.com/tlaplus/tlaplus/issues/272)
VARIABLES B, P, C
consts == <<B, P, C>>

(*ASSUME*) Constant ==
    /\ B \in 1..BufCapacity
    /\ P \in SUBSET Producers
    /\ C \in SUBSET Consumers
    /\ [][B = B' /\ P = P' /\ C = C']_consts

ConstInit ==
    /\ B \in 1..BufCapacity
    /\ P \in (SUBSET Producers \ {{}})
    /\ C \in (SUBSET Consumers \ {{}})

VARIABLES buffer, waitSet, prod, cons
vars == <<B, P, C, buffer, waitSet, prod, cons>>

-----------------------------------------------------------------------------

NotifyOther(t) == 
          LET S == IF t \in Producers THEN waitSet \ Producers ELSE waitSet \ Consumers
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Poison == CHOOSE v : TRUE

Put(t, d) ==
    /\ UNCHANGED <<prod, cons>>
    /\ t \notin waitSet
    /\ \/ /\ Len(buffer) < B
          /\ buffer' = Append(buffer, d)
          /\ NotifyOther(t)
       \/ /\ Len(buffer) = B
          /\ Wait(t)

Get(t) ==
    /\ UNCHANGED <<prod>>
    /\ t \notin waitSet
    /\ \/ /\ buffer # <<>>
          /\ buffer' = Tail(buffer)
          /\ NotifyOther(t)
          /\ IF Head(buffer) = Poison
             \* A "poison pill" terminates this consumer.
             THEN cons' = cons \ {t}
             ELSE UNCHANGED <<cons>>
       \/ /\ buffer = <<>>
          /\ Wait(t)
          /\ UNCHANGED <<cons>>

\* Producers can terminate at any time unless blocked/waiting.
Terminate(t) ==
    /\ UNCHANGED <<buffer, waitSet, cons>>
    /\ t \notin waitSet
    /\ prod' = prod \ {t}

(* 
  A dedicated "janitor" process sends a poisonous pill to each Consumer after
  all producers have terminated. The poisoned pill causes the Consumers to
  terminate in turn.  Synchronization between the Producers and the Janitor is
  left implicit. Possible implementations are discussed below.
*)
Cleanup ==
    \* An implementation could use e.g. a Phaser that Producers arrive
    \* one, and cleanup runs as part of the phaser's onadvance. Obviously,
    \* this simply delegates part of the problem we are trying to solve
    \* to another concurrency primitive, which might be acceptable but
    \* cannot be considered elegant.
    /\ prod = {}
    \* This could be implemented with a basic counter that keeps track of
    \* the number of Consumers that still have to receive a Poison Pill.
    /\ cons # {}
    /\ \/ buffer = <<>>
       \* ...there a fewer Poison messages in the buffer than (non-terminated)
       \* Consumers.
       \/ Cardinality(cons) < Cardinality({i \in DOMAIN buffer: buffer[i]=Poison})
    \* Make one of the producers the janitor that cleans up (we always
    \* choose the same janitor). An implementation may simply create a fresh
    \* process/thread (here it would be a nuisance because of TypeInv...).
    /\ Put(CHOOSE p \in P: TRUE, Poison)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ ConstInit
        /\ prod = P
        /\ cons = C
        /\ buffer = <<>>
        /\ waitSet = {}
        
(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == 
    /\ UNCHANGED consts
    /\ \/ \E p \in prod: Put(p, p)
       \/ \E p \in prod: Terminate(p)
       \/ \E c \in cons: Get(c)
       \/ Cleanup
        
-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == 
    /\ buffer \in Seq(P \cup {Poison})
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSet \in SUBSET (C \cup P)
    /\ prod \in SUBSET P
    /\ cons \in SUBSET C

(* No Deadlock *)
NoDeadlock == waitSet # (Producers \cup Consumers)

\* The queue is empty after (global) termination.
QueueEmpty ==
    ((prod \cup cons) = {}) => (buffer = <<>>)

\* The system terminates iff all producers terminate.
GlobalTermination ==
    (prod = {}) ~> [](cons = {})

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next) 

-----------------------------------------------------------------------------
\* This spec still implementes the high-level BlockingQueue spec.

BQ == INSTANCE BlockingQueue
                \* Replace Poison with some Producer. The high-level
                \* BlockingQueue spec is a peculiar about the elements
                \* in its buffer.  If this wouldn't be a tutotial but
                \* a real-world spec, the high-level spec would be
                \* corrected to be oblivious to the elements in buffer.
                WITH buffer <-
                    [ i \in DOMAIN buffer |-> IF buffer[i] = Poison
                                              THEN CHOOSE p \in Producers: TRUE
                                              ELSE buffer[i] ]

BQSpec == BQ!Spec

THEOREM Spec => BQSpec

=============================================================================

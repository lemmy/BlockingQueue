-------------------------- MODULE ProducerConsumer --------------------------
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

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

NotifyOther(t) == 
          LET S == IF t \in Producers THEN waitSet \ Producers ELSE waitSet \ Consumers
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t) ==
/\ t \notin waitSet
/\ \/ /\ buffer < BufCapacity
      /\ buffer' = buffer + 1
      /\ NotifyOther(t)
   \/ /\ buffer = BufCapacity
      /\ Wait(t)
      
Get(t) ==
/\ t \notin waitSet
/\ \/ /\ buffer > 0
      /\ buffer' = buffer - 1
      /\ NotifyOther(t)
   \/ /\ buffer = 0
      /\ Wait(t)

-----------------------------------------------------------------------------

Init == /\ buffer = 0
        /\ waitSet = {}

Next == \/ \E p \in Producers: Put(p)
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeInv == /\ buffer \in 0..BufCapacity
           /\ waitSet \in SUBSET (Producers \cup Consumers)

Invariant == waitSet # (Producers \cup Consumers)

-----------------------------------------------------------------------------

INSTANCE TLAPS

USE Assumption DEF vars, RunningThreads,
                   Init, Next, Spec,
                   Put, Get,
                   Wait, NotifyOther,
                   TypeInv, Invariant

LEMMA TypeCorrect == Spec => []TypeInv
<1>1. Init => TypeInv BY SMT 
<1>2. TypeInv /\ [Next]_vars => TypeInv' BY SMT 
<1>. QED BY <1>1, <1>2, PTL

IInv == /\ TypeInv
        /\ Invariant
        /\ buffer = 0 => \E p \in Producers : p \notin waitSet
        /\ buffer = BufCapacity => \E c \in Consumers : c \notin waitSet

THEOREM DeadlockFreedom == Spec => []Invariant
<1>1. Init => IInv BY SMT DEF IInv
<1>2. IInv /\ [Next]_vars => IInv' BY DEF IInv
<1>3. IInv => Invariant  BY DEF IInv
<1>4. QED BY <1>1,<1>2,<1>3,PTL

=============================================================================

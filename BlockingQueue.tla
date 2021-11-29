--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)
          ,Feature

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       /\ Feature \in {"no", "na"}
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

NotifyOther(t) == 
          LET S == IF t \in Producers THEN waitSet \ Producers ELSE waitSet \ Consumers
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

acquire == 0
worked  == 1
ASSUME TLCSet(acquire, 0) /\ TLCSet(worked, 0)

Put(t, d) ==
/\ t \notin waitSet
\* /\ TLCSet(acquire, TLCGet(acquire)+1)
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ IF Feature = "no" THEN NotifyOther(t) ELSE waitSet' = {}
      /\ TLCSet(worked, TLCGet(worked)+1)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)

Get(t) ==
/\ t \notin waitSet
\* /\ TLCSet(acquire, TLCGet(acquire)+1)
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
    /\ IF Feature = "no" THEN NotifyOther(t) ELSE waitSet' = {}
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == 
    /\ TLCGet("level") = 1 => (TLCSet(acquire, 0) /\ TLCSet(worked, 0))
    /\ \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
       \/ \E c \in Consumers: Get(c)

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \in SUBSET (Producers \cup Consumers)

(* No Deadlock *)
Invariant == waitSet # (Producers \cup Consumers)

-----------------------------------------------------------------------------

MySeq(P) == UNION {[1..n -> P] : n \in 0..BufCapacity}

INSTANCE TLAPS

Spec == Init /\ [][Next]_vars

(* Whitelist all the known facts and definitions (except IInv below) *)
USE Assumption DEF vars, RunningThreads,
                   Init, Next, Spec,
                   Put, Get,
                   Wait, NotifyOther,
                   TypeInv, Invariant

\* TypeInv will be a conjunct of the inductive invariant, so prove it inductive.
\* An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* though, that TypeInv itself won't imply Invariant though!  TypeInv alone
\* does not help us prove Invariant.
\* Luckily, TLAPS does not require us to decompose the proof into substeps. 
LEMMA TypeCorrect == Spec => []TypeInv
<1>1. Init => TypeInv BY SMT 
<1>2. TypeInv /\ [Next]_vars => TypeInv' BY SMT 
<1>. QED BY <1>1, <1>2, PTL

\* The naive thing to do is to check if the conjunct of TypeInv /\ Invariant
\* is inductive.
IInv == /\ TypeInv!2
        /\ TypeInv!3
        /\ Invariant
        \* When the buffer is empty, a consumer will be added to the waitSet.
        \* However, this does not crate a deadlock, because at least one producer
        \* will not be in the waitSet.
        /\ buffer = <<>> => \E p \in Producers : p \notin waitSet
        \* Vice versa, when buffer is full, a producer will be added to waitSet,
        \* but at least one consumer won't be in waitSet.
        /\ Len(buffer) = BufCapacity => \E c \in Consumers : c \notin waitSet

THEOREM DeadlockFreedom == Spec => []Invariant
<1>1. Init => IInv BY SMT DEF IInv
<1>2. IInv /\ [Next]_vars => IInv' BY DEF IInv
<1>3. IInv => Invariant  BY DEF IInv
<1>4. QED BY <1>1,<1>2,<1>3,PTL

MCIInv == TypeInv!1 /\ IInv

-----------------------------------------------------------------------------

PutEnabled == \A p \in Producers : ENABLED Put(p, p)

FairSpec == 
    /\ Spec

    \* Assert that producers take steps should their  Put  action be (continuously) 
    \* enabled. This is the basic case of fairness that rules out stuttering, i.e.,
    \* assert global progress.
    /\ \A t \in Producers:
            WF_vars(Put(t,t)) 
    \* Stipulates that  Get  actions (consumers!) will eventually notify *all*
    \* waiting producers. In other words, given repeated  Get  actions (we don't
    \* care which consumer, thus, existential quantification), all waiting
    \* producers will eventually be notified.  Because  Get  actions are not
    \* continuously enabled (the buffer might be empty), weak fairness is not
    \* strong enough. Obviously, no real system scheduler implements such an
    \* inefficient "policy".
    \* This fairness constraint was initially proposed by Leslie Lamport, although
    \* with the minor typo "in" instead of "notin", which happens to hold for
    \* configurations with at most two producers.
    /\ \A t \in Producers:
            SF_vars(\E self \in Consumers: Get(self) /\ t \notin waitSet')

    \* See notes above (except swap "producer" with "consumer").
    /\ \A t \in Consumers:
            WF_vars(Get(t)) 
    /\ \A t \in Consumers:
            SF_vars(\E self \in Producers: Put(self, self) /\ t \notin waitSet')

(* All producers will continuously be serviced. For this to be violated,    *)
(* ASSUME Cardinality(Producers) > 1 has to hold (a single producer cannot  *)
(* starve itself).                                                          *)
Starvation ==
    /\ \A p \in Producers: []<>(<<Put(p, p)>>_vars)
    /\ \A c \in Consumers: []<>(<<Get(c)>>_vars)

=============================================================================

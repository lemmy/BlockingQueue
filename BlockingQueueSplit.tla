------------------------- MODULE BlockingQueueSplit -------------------------
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

VARIABLES buffer, waitSetC, waitSetP
vars == <<buffer, waitSetC, waitSetP>>

RunningThreads == (Producers \cup Consumers) \ (waitSetC \cup waitSetP)

NotifyOther(ws) == 
         \/ /\ ws = {}
            /\ UNCHANGED ws
         \/ /\ ws # {}
            /\ \E x \in ws: ws' = ws \ {x}

(* @see java.lang.Object#wait *)
Wait(ws, t) == /\ ws' = ws \cup {t}
               /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin waitSetP
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(waitSetC)
      /\ UNCHANGED waitSetP
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(waitSetP, t)
      /\ UNCHANGED waitSetC
      
Get(t) ==
/\ t \notin waitSetC
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(waitSetP)
      /\ UNCHANGED waitSetC
   \/ /\ buffer = <<>>
      /\ Wait(waitSetC, t)
      /\ UNCHANGED waitSetP

-----------------------------------------------------------------------------

TypeInv == /\ buffer \in Seq(Producers) 
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSetP \in SUBSET Producers
           /\ waitSetC \in SUBSET Consumers

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSetC = {}
        /\ waitSetP = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(* BlockingQueueSplit refines BlockingQueue. The refinement mapping is *)
(* straight forward in this case. The union of waitSetC and waitSetP   *)
(* maps to waitSet in the high-level spec BlockingQueue.               *)
A == INSTANCE BlockingQueue WITH waitSet <- (waitSetC \cup waitSetP)

(* A!Spec is not a valid value in the config BlockingQueueSplit.cfg.   *)
ASpec == A!Spec

-----------------------------------------------------------------------------

INSTANCE TLAPS

(* Scaffolding: TypeInv is inductive. *)
LEMMA ITypeInv == Spec => []TypeInv
<1> USE Assumption DEF TypeInv
<1>1. Init => TypeInv
  BY DEF Init
<1>2. TypeInv /\ [Next]_vars => TypeInv'
  BY DEF Next, vars, Put, Get, Wait, NotifyOther
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Implements == Spec => A!Spec
<1> USE Assumption, A!Assumption
<1>1. Init => A!Init 
   BY DEF Init, A!Init
<1>2. TypeInv /\ [Next]_vars => [A!Next]_A!vars
   BY DEF TypeInv, Next, vars, Put, Get, Wait, NotifyOther, A!Next, 
          A!vars, A!Put, A!Get, A!Wait, A!NotifyOther, A!RunningThreads
<1>3. QED BY <1>1, <1>2, PTL, ITypeInv DEF Spec, A!Spec


-----------------------------------------------------------------------------

(* The IInv below mirrors the high-level BlockingQueue!IInv translated to *)
(* the split form: keep TypeInv!2 (Len) and the wait-set domain           *)
(* constraints, the deadlock-freedom Invariant on the union, and the same *)
(* two existential clauses guarding the buffer = <<>> and full buffer     *)
(* cases.                                                                 *)
(*                                                                        *)
(* Strictly speaking, proving DeadlockFreedom directly here is redundant: *)
(* the THEOREM Implements above already establishes Spec => A!Spec, hence *)
(* []A!Invariant transfers to BlockingQueueSplit by refinement. We prove  *)
(* it locally as scaffolding/illustration of the inductive invariant.     *)
IInv ==
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSetP \in SUBSET Producers
    /\ waitSetC \in SUBSET Consumers
    /\ (waitSetC \cup waitSetP) # (Producers \cup Consumers)
    /\ buffer = <<>> => \E p \in Producers : p \notin (waitSetC \cup waitSetP)
    /\ Len(buffer) = BufCapacity => \E c \in Consumers : c \notin (waitSetC \cup waitSetP)

(* This proof of deadlock freedom is self-contained: it only references  *)
(* A!Invariant (the predicate) and never relies on BlockingQueue's       *)
(* state machine (A!Init, A!Next, A!Spec) or its inductive invariant     *)
(* A!IInv.                                                               *)
THEOREM DeadlockFreedom == Spec => []A!Invariant
<1> USE Assumption, ITypeInv DEF IInv, TypeInv, A!Invariant
<1>1. Init => IInv BY DEF Init
<1>2. TypeInv /\ IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME TypeInv, IInv, [Next]_vars
               PROVE  IInv' OBVIOUS
  <2>1. ASSUME NEW p \in Producers, Put(p, p)
        PROVE  IInv' BY <2>1 DEF Put, Wait, NotifyOther, vars
  <2>2. ASSUME NEW c \in Consumers, Get(c)
        PROVE  IInv' BY <2>2 DEF Get, Wait, NotifyOther, vars
  <2>3. CASE UNCHANGED vars BY <2>3 DEF vars
  <2>4. QED BY <2>1, <2>2, <2>3 DEF Next
<1>3. IInv => A!Invariant OBVIOUS
<1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

(* IInv matches A!IInv up to splitting the wait-set constraint into its  *)
(* Producers/Consumers components, hence implies it pointwise. Combined  *)
(* with THEOREM Implements (Spec => A!Spec), this gives an alternative,  *)
(* refinement-based route to deadlock freedom that does not require the  *)
(* self-contained inductive proof of DeadlockFreedom above.              *)
THEOREM IInvRefines == ASSUME IInv PROVE A!IInv
  BY Assumption DEF IInv, A!IInv, A!TypeInv, A!Invariant

=============================================================================

------------------------- MODULE BlockingQueueFair -------------------------
EXTENDS Naturals, Sequences, FiniteSets, Functions, SequencesExt, SequencesExtTheorems

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ Consumers \intersect Producers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSeqC, waitSeqP
vars == <<buffer, waitSeqC, waitSeqP>>

WaitingThreads == Range(waitSeqC) \cup Range(waitSeqP)

RunningThreads == (Producers \cup Consumers) \ WaitingThreads

NotifyOther(ws) ==
            \/ /\ ws = <<>>
               /\ UNCHANGED ws
            \/ /\ ws # <<>>
               /\ ws' = Tail(ws)

(* @see java.lang.Object#wait *)
Wait(ws, t) == 
            /\ ws' = Append(ws, t)
            /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin Range(waitSeqP)
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(waitSeqC)
      /\ UNCHANGED waitSeqP
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(waitSeqP, t)
      /\ UNCHANGED waitSeqC
      
Get(t) ==
/\ t \notin Range(waitSeqC)
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(waitSeqP)
      /\ UNCHANGED waitSeqC
   \/ /\ buffer = <<>>
      /\ Wait(waitSeqC, t)
      /\ UNCHANGED waitSeqP

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars 

FairSpec == Spec /\ \A c \in Consumers : WF_vars(Get(c)) 
                 /\ \A p \in Producers : WF_vars(Put(p, p)) 

----------------

BQS == INSTANCE BlockingQueueSplit WITH waitSetC <- Range(waitSeqC), 
                                        waitSetP <- Range(waitSeqP)

BQSSpec == BQS!Spec
THEOREM Spec => BQSSpec

BQSFairSpec == BQS!A!FairSpec
THEOREM FairSpec => BQSFairSpec

BQSStarvation == BQS!A!Starvation
THEOREM FairSpec => BQSStarvation
-----------------------------------------------------------------------------

TypeInv == /\ Len(buffer) \in 0..BufCapacity
           \* Producers
           /\ waitSeqP \in Seq(Producers)
           /\ IsInjective(waitSeqP) \* no duplicates (thread is either asleep or not)!
           \* Consumers
           /\ waitSeqC \in Seq(Consumers)
           /\ IsInjective(waitSeqC) \* no duplicates (thread is either asleep or not)!

INSTANCE TLAPS

(* Prove TypeInv inductive. *)
THEOREM ITypeInv == Spec => []TypeInv
<1> USE Assumption DEF Range, TypeInv
<1>1. Init => TypeInv 
    BY DEF Init, IsInjective
<1>2. TypeInv /\ [Next]_vars => TypeInv'
  <2> SUFFICES ASSUME TypeInv,
                      [Next]_vars
               PROVE  TypeInv'
    OBVIOUS
  <2>1. ASSUME NEW p \in Producers,
               Put(p, p)
        PROVE  TypeInv'
    <3>1. CASE /\ Len(buffer) < BufCapacity
               /\ buffer' = Append(buffer, p)
               /\ NotifyOther(waitSeqC)
               /\ UNCHANGED waitSeqP
      BY <3>1, <2>1, TailTransitivityIsInjective
      DEF NotifyOther, IsInjective
    <3>2. CASE /\ Len(buffer) = BufCapacity
               /\ Wait(waitSeqP, p)
               /\ UNCHANGED waitSeqC
      \* Put below so TLAPS knows about t \notin Range(waitSeqP)
      BY <3>2, <2>1, AppendTransitivityIsInjective
      DEF Wait, IsInjective, Put
    <3>3. QED
      BY <2>1, <3>1, <3>2 DEF Put
  <2>2. ASSUME NEW c \in Consumers,
               Get(c)
        PROVE  TypeInv'
    <3>1. CASE /\ buffer # <<>>
               /\ buffer' = Tail(buffer)
               /\ NotifyOther(waitSeqP)
               /\ UNCHANGED waitSeqC
      BY <3>1, <2>2, TailTransitivityIsInjective
      DEF NotifyOther, IsInjective
    <3>2. CASE /\ buffer = <<>>
               /\ Wait(waitSeqC, c)
               /\ UNCHANGED waitSeqP
      \* Get below so TLAPS knows about t \notin Range(waitSeqC)
      BY <3>2, <2>2, AppendTransitivityIsInjective
      DEF Wait, IsInjective, Get
    <3>3. QED
      BY <2>2, <3>1, <3>2 DEF Get
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
=============================================================================

---------------------- MODULE BlockingQueueFair_proofs ----------------------
EXTENDS BlockingQueueFair, SequenceTheorems, TLAPS

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
      BY <3>1, <2>1, TailInjectiveSeq
      DEF NotifyOther, IsInjective
    <3>2. CASE /\ Len(buffer) = BufCapacity
               /\ Wait(waitSeqP, p)
               /\ UNCHANGED waitSeqC
      \* Put below so TLAPS knows about t \notin Range(waitSeqP)
      BY <3>2, <2>1, AppendInjectiveSeq
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
      BY <3>1, <2>2, TailInjectiveSeq, HeadTailProperties
      DEF NotifyOther, IsInjective
    <3>2. CASE /\ buffer = <<>>
               /\ Wait(waitSeqC, c)
               /\ UNCHANGED waitSeqP
      \* Get below so TLAPS knows about t \notin Range(waitSeqC)
      BY <3>2, <2>2, AppendInjectiveSeq
      DEF Wait, IsInjective, Get
    <3>3. QED
      BY <2>2, <3>1, <3>2 DEF Get
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

=============================================================================

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

-----------------------------------------------------------------------------

LEMMA EmptySeqRange == ASSUME NEW S, NEW seq \in Seq(S)
                       PROVE seq = <<>> <=> Range(seq) = {}
BY Isa DEF Range

LEMMA RangeTail == 
  ASSUME NEW S, NEW ws \in Seq(S), IsInjective(ws)
         , ws # <<>>
  PROVE \E x \in Range(ws): Range(Tail(ws)) = Range(ws) \ {x}
\* BY Z3 DEF Range, IsInjective \* Proof goes through with Tail
                                \* re-defined with the CASE
                                \* statement omitted, which is
                                \* equivalent here due to
                                \* 'ws # <<>>' assumption.

-----------------------------------------------------------------------------

(* Prove BlockingQueueFair implements BlockingQueueSplit *)
THEOREM Spec => BQS!Spec
<1> USE Assumption DEF Range
<1>1. Init => BQS!Init 
   BY DEF Init, BQS!Init
<1>2. TypeInv /\ [Next]_vars => [BQS!Next]_BQS!vars
  <2> SUFFICES ASSUME TypeInv,
                      [Next]_vars
               PROVE  [BQS!Next]_BQS!vars
    OBVIOUS
  <2>1. ASSUME NEW p \in Producers,
               Put(p, p)
        PROVE  [BQS!Next]_BQS!vars
    <3>1. CASE /\ Len(buffer) < BufCapacity
               /\ buffer' = Append(buffer, p)
               /\ NotifyOther(waitSeqC)
               /\ UNCHANGED waitSeqP
      <4>1. CASE /\ waitSeqC = <<>>
                 /\ UNCHANGED waitSeqC
        BY <4>1, <2>1, <3>1, Isa 
        DEF Put, BQS!Next, BQS!vars, BQS!Put, BQS!NotifyOther
      <4>2. CASE /\ waitSeqC # <<>>
                 /\ waitSeqC' = Tail(waitSeqC)
        BY <4>2, <2>1, <3>1, EmptySeqRange, RangeTail, Isa
        DEF TypeInv, Put, BQS!Next, BQS!vars, BQS!Put, BQS!NotifyOther
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF NotifyOther
    <3>2. CASE /\ Len(buffer) = BufCapacity
               /\ Wait(waitSeqP, p)
               /\ UNCHANGED waitSeqC
      <4>1. waitSeqP \in Seq(Producers) /\ waitSeqP' = Append(waitSeqP, p)
        BY <3>2 DEF Wait, TypeInv
      <4>2. Range(Append(waitSeqP, p)) = Range(waitSeqP) \cup {p}
        BY <4>1, AppendProperties
      <4>3. BQS!Put(p, p)
        BY <2>1, <3>2, <4>1, <4>2 DEF Put, Wait, BQS!Put, BQS!Wait
      <4>. QED
        BY <2>1, <3>2, <4>3 DEF BQS!Next, BQS!vars, Wait
    <3>3. QED
      BY <2>1, <3>1, <3>2 DEF Put
  <2>2. ASSUME NEW c \in Consumers,
               Get(c)
        PROVE  [BQS!Next]_BQS!vars
    <3>1. CASE /\ buffer # <<>>
               /\ buffer' = Tail(buffer)
               /\ NotifyOther(waitSeqP)
               /\ UNCHANGED waitSeqC
      <4>1. CASE /\ waitSeqP = <<>>
                 /\ UNCHANGED waitSeqP
        BY <4>1, <2>2, <3>1, Isa 
        DEF Get, BQS!Next, BQS!vars, BQS!Get, BQS!NotifyOther
      <4>2. CASE /\ waitSeqP # <<>>
                 /\ waitSeqP' = Tail(waitSeqP)
        BY <4>2, <2>2, <3>1, EmptySeqRange, RangeTail, Isa
        DEF TypeInv, Get, BQS!Next, BQS!vars, BQS!Get, BQS!NotifyOther
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF NotifyOther
    <3>2. CASE /\ buffer = <<>>
               /\ Wait(waitSeqC, c)
               /\ UNCHANGED waitSeqP
      <4>1. waitSeqC \in Seq(Consumers) /\ waitSeqC' = Append(waitSeqC, c)
        BY <3>2 DEF Wait, TypeInv
      <4>2. Range(Append(waitSeqC, c)) = Range(waitSeqC) \cup {c}
        BY <4>1, AppendProperties
      <4>3. BQS!Get(c)
        BY <2>2, <3>2, <4>1, <4>2 DEF Get, Wait, BQS!Get, BQS!Wait
      <4>. QED
        BY <2>2, <3>2, <4>3 DEF BQS!Next, BQS!vars, Wait
    <3>3. QED
      BY <2>2, <3>1, <3>2 DEF Get
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, BQS!Next, BQS!vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED BY <1>1, <1>2, ITypeInv, PTL DEF Spec, BQS!Spec

=============================================================================

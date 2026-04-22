------------------- MODULE BlockingQueuePoisonApple_proofs ------------------
(***************************************************************************)
(* TLAPS proofs for the BlockingQueuePoisonApple module.  Kept in a        *)
(* separate file so that the main specification stays free of TLAPS-       *)
(* related INSTANCE statements and assumptions.                            *)
(*                                                                         *)
(* Run with                                                                *)
(*   tlapm --nofp -I /path/to/CommunityModules/modules                     *)
(*       BlockingQueuePoisonApple_proofs.tla                               *)
(* so that the CommunityModules theorem files                              *)
(* (FunctionTheorems with SumFunction theorems) are visible to TLAPS.      *)
(***************************************************************************)
EXTENDS BlockingQueuePoisonApple

INSTANCE TLAPS
INSTANCE FiniteSetTheorems
INSTANCE SequenceTheorems
INSTANCE FunctionTheorems

ASSUME FinAssumption ==
    /\ IsFiniteSet(Producers)
    /\ IsFiniteSet(Consumers)
    /\ Poison \notin Producers

(***************************************************************************)
(* Step 1: TypeInv is itself inductive and is therefore a stand-alone      *)
(* invariant of  Spec .                                                    *)
(***************************************************************************)
LEMMA TypeInvInit == Init => TypeInv
  BY Assumption, FinAssumption, FS_CardinalityType, EmptySeq DEF TypeInv, Init

LEMMA TypeInvInductive == TypeInv /\ [Next]_vars => TypeInv'
<1> USE Assumption, FinAssumption, FS_CardinalityType
       DEF TypeInv, vars, NotifyOther, Wait
<1> SUFFICES ASSUME TypeInv, [Next]_vars PROVE TypeInv' OBVIOUS
<1>1. ASSUME NEW p \in Producers, Put(p, p) PROVE TypeInv'
  BY <1>1, AppendProperties DEF Put
<1>2. ASSUME NEW c \in Consumers, Get(c) PROVE TypeInv'
  BY <1>2, HeadTailProperties DEF Get
<1>. QED BY <1>1, <1>2 DEF Next

LEMMA TypeCorrect == Spec => []TypeInv
  BY TypeInvInit, TypeInvInductive, PTL DEF Spec

(***************************************************************************)
(* Step 2: NoDeadlock follows from a strengthened invariant DInv that      *)
(* contains the two existential clauses guarding the empty / full buffer.  *)
(***************************************************************************)
DInv ==
    /\ NoDeadlock
    /\ (buffer = <<>>) => \E p \in Producers : p \notin waitSet
    /\ (Len(buffer) = BufCapacity) => \E c \in Consumers : c \notin waitSet

THEOREM Safety == Spec => []NoDeadlock
<1> USE Assumption, FinAssumption
       DEF TypeInv, NoDeadlock, DInv, vars, Wait, NotifyOther
<1>1. Init => DInv BY EmptySeq DEF Init
<1>2. TypeInv /\ DInv /\ [Next]_vars => DInv'
  <2> SUFFICES ASSUME TypeInv, DInv, [Next]_vars PROVE DInv' OBVIOUS
  <2>1. ASSUME NEW p \in Producers, Put(p, p) PROVE DInv'  BY <2>1 DEF Put
  <2>2. ASSUME NEW c \in Consumers, Get(c) PROVE DInv'     BY <2>2 DEF Get
  <2>. QED BY <2>1, <2>2 DEF Next
<1>. QED BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

(***************************************************************************)
(* Step 3: QueueEmpty.  Strengthen QueueEmpty into the inductive QInv:     *)
(*   (A) Cardinality(PoisonsInBuf) + SumFunction(prod) = SumFunction(cons).*)
(*       The total of the remaining producer credits  prod[p]  plus the    *)
(*       number of Poison items in the buffer equals the total of the     *)
(*       remaining consumer credits  cons[c] .                             *)
(*   (B) FIFO ordering.  Every non-Poison item in the buffer is followed   *)
(*       by a Poison further back, or some producer is still active.       *)
(* Together (A) and (B) force buffer to be empty whenever ap = ac = {}.    *)
(***************************************************************************)

\* Index set of Poison occurrences in the buffer.
PoisonSet(buf)  == { i \in 1..Len(buf) : buf[i] = Poison }
PoisonsInBuf    == PoisonSet(buffer)

QInv ==
    /\ Cardinality(PoisonsInBuf) + SumFunction(prod) = SumFunction(cons)
    /\ \A i \in 1..Len(buffer) : buffer[i] # Poison =>
            (\E p \in Producers : prod[p] > 0)
         \/ (\E j \in (i+1)..Len(buffer) : buffer[j] = Poison)

(***************************************************************************)
(* Auxiliary lemmas about PoisonSet under Append and Tail.                 *)
(***************************************************************************)

LEMMA PoisonSetFinite ==
    ASSUME NEW buf \in Seq(Producers \cup {Poison})
    PROVE  IsFiniteSet(PoisonSet(buf))
  BY FS_Interval, FS_Subset DEF PoisonSet

LEMMA PoisonAppendOther ==
    ASSUME NEW buf \in Seq(Producers \cup {Poison}),
           NEW x \in Producers \cup {Poison}, x # Poison
    PROVE  PoisonSet(Append(buf, x)) = PoisonSet(buf)
  BY AppendProperties, LenProperties DEF PoisonSet

LEMMA PoisonAppendPoison ==
    ASSUME NEW buf \in Seq(Producers \cup {Poison})
    PROVE  /\ PoisonSet(Append(buf, Poison)) = PoisonSet(buf) \cup {Len(buf) + 1}
           /\ Cardinality(PoisonSet(Append(buf, Poison)))
                 = Cardinality(PoisonSet(buf)) + 1
<1>1. PoisonSet(Append(buf, Poison)) = PoisonSet(buf) \cup {Len(buf) + 1}
  BY AppendProperties, LenProperties DEF PoisonSet
<1>2. (Len(buf) + 1) \notin PoisonSet(buf)
  BY LenProperties DEF PoisonSet
<1>. QED  BY <1>1, <1>2, PoisonSetFinite, FS_AddElement

LEMMA PoisonTail ==
    ASSUME NEW buf \in Seq(Producers \cup {Poison}), buf # <<>>
    PROVE  Cardinality(PoisonSet(Tail(buf)))
              = Cardinality(PoisonSet(buf)) - (IF Head(buf) = Poison THEN 1 ELSE 0)
<1> USE FinAssumption
<1> DEFINE n     == Len(buf)
<1> DEFINE Shift == { j \in 2..n : buf[j] = Poison }
<1>1. /\ Len(Tail(buf)) = n - 1 /\ n \in Nat /\ n >= 1
      /\ \A i \in 1..(n-1) : Tail(buf)[i] = buf[i + 1]
      /\ Head(buf) = buf[1]
  BY HeadTailProperties, LenProperties, EmptySeq
<1>2. IsFiniteSet(Shift)
  BY FS_Interval, FS_Subset
<1>3. PoisonSet(Tail(buf)) = { i \in 1..(n - 1) : buf[i + 1] = Poison }
  BY <1>1 DEF PoisonSet
<1>4. Cardinality(PoisonSet(Tail(buf))) = Cardinality(Shift)
  <2> DEFINE f == [i \in PoisonSet(Tail(buf)) |-> i + 1]
  <2>1. f \in Bijection(PoisonSet(Tail(buf)), Shift)
    <3>1. f \in [PoisonSet(Tail(buf)) -> Shift]   BY <1>3, <1>1
    <3>2. \A i, j \in PoisonSet(Tail(buf)) : f[i] = f[j] => i = j  BY <1>3
    <3>3. \A k \in Shift : \E i \in PoisonSet(Tail(buf)) : f[i] = k
      <4> SUFFICES ASSUME NEW k \in Shift
                   PROVE  \E i \in PoisonSet(Tail(buf)) : f[i] = k
        OBVIOUS
      <4>1. (k - 1) \in PoisonSet(Tail(buf)) /\ f[k - 1] = k
        BY <1>3, <1>1
      <4>. QED  BY <4>1
    <3>. QED  BY <3>1, <3>2, <3>3, Fun_IsBij
  <2>2. IsFiniteSet(PoisonSet(Tail(buf)))
    BY <1>3, <1>1, FS_Interval, FS_Subset
  <2>. QED  BY <2>1, <2>2, FS_Bijection DEF ExistsBijection
<1>5. CASE Head(buf) = Poison
  <2>1. PoisonSet(buf) = Shift \cup {1}
    <3> SUFFICES ASSUME NEW i \in 1..n
                 PROVE  (buf[i] = Poison) <=> (i \in Shift \/ i = 1)
      BY DEF PoisonSet
    <3>. QED  BY <1>1, <1>5
  <2>. QED  BY <2>1, <1>4, <1>5, <1>2, FS_AddElement, FS_CardinalityType
<1>6. CASE Head(buf) # Poison
  <2>1. PoisonSet(buf) = Shift
    <3> SUFFICES ASSUME NEW i \in 1..n
                 PROVE  (buf[i] = Poison) <=> i \in Shift
      BY DEF PoisonSet
    <3>. QED  BY <1>1, <1>6
  <2>. QED  BY <2>1, <1>4, <1>6, <1>2, FS_CardinalityType
<1>. QED  BY <1>5, <1>6

(***************************************************************************)
(* The QInv components are well-typed.                                     *)
(***************************************************************************)
LEMMA QInvTypes ==
    ASSUME TypeInv
    PROVE  /\ SumFunction(prod) \in Nat
           /\ SumFunction(cons) \in Nat
           /\ Cardinality(PoisonsInBuf) \in Nat
  BY FinAssumption, FS_CardinalityType, SumFunctionNat, PoisonSetFinite
     DEF TypeInv, PoisonsInBuf

(***************************************************************************)
(* Main inductive proof.                                                   *)
(***************************************************************************)
THEOREM QueueEmptyTheorem == Spec => QueueEmpty
<1> DEFINE Inv == TypeInv /\ QInv
<1> USE Assumption, FinAssumption, FS_CardinalityType
       DEF TypeInv, vars, NotifyOther, Wait, ap, ac, QueueEmpty, QInv
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <2>1. TypeInv  BY EmptySeq DEF Init
  <2>2. PoisonsInBuf = {} /\ Cardinality(PoisonsInBuf) = 0
    BY EmptySeq, FS_EmptySet DEF PoisonsInBuf, PoisonSet, Init
  <2>3. SumFunction(prod) = Cardinality(Consumers) * Cardinality(Producers)
    BY SumFunctionConst DEF Init
  <2>4. SumFunction(cons) = Cardinality(Producers) * Cardinality(Consumers)
    BY SumFunctionConst DEF Init
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, EmptySeq DEF Init
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <2>0. TypeInv'  BY TypeInvInductive
  <2> USE QInvTypes DEF Inv
  <2>1. ASSUME NEW p \in Producers, Put(p, p)  PROVE  QInv'
    <3> USE <2>1
    <3>0. /\ prod \in [Producers -> 0..Cardinality(Consumers)]
          /\ buffer \in Seq(Producers \cup {Poison})
          /\ p \in Producers \cup {Poison}
          /\ DOMAIN prod = Producers
      BY DEF TypeInv
    <3>1. CASE /\ Len(buffer) < BufCapacity
               /\ buffer' = Append(buffer, p)
               /\ UNCHANGED prod
               /\ NotifyOther(Consumers)
               /\ UNCHANGED <<cons>>
      <4> USE <3>1
      <4>1. p # Poison  BY DEF TypeInv
      <4>2. PoisonsInBuf' = PoisonsInBuf
        BY <4>1, <3>0, PoisonAppendOther DEF PoisonsInBuf
      <4>3. \A i \in 1..Len(buffer') : buffer'[i] # Poison =>
              (\E q \in Producers : prod'[q] > 0)
              \/ (\E j \in (i+1)..Len(buffer') : buffer'[j] = Poison)
        BY DEF Put
      <4>. QED  BY <4>2, <4>3
    <3>2. CASE /\ Len(buffer) < BufCapacity
               /\ buffer' = Append(buffer, Poison)
               /\ prod' = [ prod EXCEPT ![p] = @ - 1]
               /\ NotifyOther(Consumers)
               /\ UNCHANGED <<cons>>
      <4> USE <3>2
      <4>1. SumFunction(prod') = SumFunction(prod) - 1
        BY <3>0, SumFunctionExcept
      <4>2. Cardinality(PoisonsInBuf') = Cardinality(PoisonsInBuf) + 1
        BY <3>0, PoisonAppendPoison DEF PoisonsInBuf
      <4>3. \A i \in 1..Len(buffer') : buffer'[i] # Poison =>
              \E j \in (i+1)..Len(buffer') : buffer'[j] = Poison
        <5> SUFFICES ASSUME NEW i \in 1..Len(buffer'), buffer'[i] # Poison
                     PROVE  \E j \in (i+1)..Len(buffer') : buffer'[j] = Poison
          OBVIOUS
        <5>1. /\ Len(buffer') = Len(buffer) + 1
              /\ buffer'[Len(buffer) + 1] = Poison
          BY AppendProperties, <3>0
        <5>2. (Len(buffer) + 1) \in (i+1)..Len(buffer')  BY <5>1
        <5>. QED  BY <5>1, <5>2
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>3. CASE /\ Len(buffer) = BufCapacity
               /\ Wait(p)
               /\ UNCHANGED prod
               /\ UNCHANGED <<cons>>
      BY <3>3 DEF Wait, PoisonsInBuf, PoisonSet
    <3>. QED  BY <3>1, <3>2, <3>3 DEF Put
  <2>2. ASSUME NEW c \in Consumers, Get(c)  PROVE  QInv'
    <3> USE <2>2
    <3>0. /\ cons \in [Consumers -> 0..Cardinality(Producers)]
          /\ buffer \in Seq(Producers \cup {Poison})
          /\ DOMAIN cons = Consumers
      BY DEF TypeInv
    \* Helper for the FIFO part of QInv: when buffer' = Tail(buffer), any
    \* non-Poison item in buffer' shifts down from a non-Poison item in
    \* buffer that was witnessed by a Poison further back.
    <3>F. ASSUME /\ buffer # <<>>
                 /\ buffer' = Tail(buffer)
                 /\ UNCHANGED prod
          PROVE  \A i \in 1..Len(buffer') : buffer'[i] # Poison =>
                    (\E q \in Producers : prod'[q] > 0)
                    \/ (\E j \in (i+1)..Len(buffer') : buffer'[j] = Poison)
      <4> USE <3>F
      <4>1. /\ Len(buffer') = Len(buffer) - 1
            /\ \A k \in 1..Len(buffer') : buffer'[k] = buffer[k+1]
        BY HeadTailProperties, <3>0
      <4> SUFFICES ASSUME NEW i \in 1..Len(buffer'), buffer'[i] # Poison
                   PROVE  (\E q \in Producers : prod'[q] > 0)
                          \/ (\E j \in (i+1)..Len(buffer') : buffer'[j] = Poison)
        OBVIOUS
      <4>2. (i+1) \in 1..Len(buffer) /\ buffer[i+1] # Poison
        BY <4>1
      <4>3. (\E q \in Producers : prod[q] > 0)
            \/ (\E j \in (i+2)..Len(buffer) : buffer[j] = Poison)
        BY <4>2
      <4>4. ASSUME NEW j \in (i+2)..Len(buffer), buffer[j] = Poison
            PROVE  \E j2 \in (i+1)..Len(buffer') : buffer'[j2] = Poison
        <5>1. (j-1) \in (i+1)..Len(buffer') /\ buffer'[j-1] = buffer[j]
          BY <4>1
        <5>. QED  BY <5>1, <4>4
      <4>. QED  BY <4>3, <4>4
    <3>1. CASE /\ buffer # <<>>
               /\ buffer' = Tail(buffer)
               /\ NotifyOther(Producers)
               /\ Head(buffer) # Poison
               /\ UNCHANGED <<prod, cons>>
      <4> USE <3>1
      <4>1. PoisonsInBuf' = PoisonSet(Tail(buffer))  BY DEF PoisonsInBuf
      <4>2. Cardinality(PoisonsInBuf') = Cardinality(PoisonsInBuf)
        BY <3>0, PoisonTail, <4>1 DEF PoisonsInBuf
      <4>. QED  BY <4>2, <3>F
    <3>2. CASE /\ buffer # <<>>
               /\ buffer' = Tail(buffer)
               /\ NotifyOther(Producers)
               /\ Head(buffer) = Poison
               /\ cons' = [ cons EXCEPT ![c] = @ - 1]
               /\ UNCHANGED <<prod>>
      <4> USE <3>2
      <4>1. SumFunction(cons') = SumFunction(cons) - 1
        BY <3>0, SumFunctionExcept
      <4>2. /\ PoisonsInBuf' = PoisonSet(Tail(buffer))
            /\ Cardinality(PoisonSet(Tail(buffer)))
                = Cardinality(PoisonSet(buffer)) - 1
        BY <3>0, PoisonTail DEF PoisonsInBuf
      <4>. QED  BY <4>1, <4>2, <3>F DEF PoisonsInBuf
    <3>3. CASE /\ buffer = <<>>
               /\ Wait(c)
               /\ UNCHANGED <<prod, cons>>
      BY <3>3 DEF Wait, PoisonsInBuf, PoisonSet
    <3>. QED  BY <3>1, <3>2, <3>3 DEF Get
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF PoisonsInBuf, PoisonSet
  <2>. QED  BY <2>0, <2>1, <2>2, <2>3 DEF Next
<1>3. Inv => (ap \cup ac = {} => buffer = <<>>)
  <2> SUFFICES ASSUME Inv, ap \cup ac = {}, buffer # <<>> PROVE FALSE  OBVIOUS
  <2>1. /\ \A p \in Producers : prod[p] = 0
        /\ \A c \in Consumers : cons[c] = 0
    OBVIOUS
  <2>2. SumFunction(prod) = 0 /\ SumFunction(cons) = 0
    BY <2>1, SumFunctionZero
  <2>3. PoisonsInBuf = {}
    BY <2>2, QInvTypes, FS_EmptySet, PoisonSetFinite DEF PoisonsInBuf
  <2>4. 1 \in 1..Len(buffer) /\ buffer[1] # Poison
    BY <2>3, EmptySeq DEF PoisonsInBuf, PoisonSet
  <2>. QED  BY <2>1, <2>3, <2>4 DEF PoisonsInBuf, PoisonSet
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================

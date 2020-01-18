------------------------ MODULE BlockingQueue_proofs ------------------------
EXTENDS BlockingQueue, TLAPS

\* TypeInv will be a conjunct of the inductive invariant, so prove it inductive.
\* An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* though, that TypeInv itself won't imply Invariant though!  TypeInv alone
\* does not help us prove Invariant.
\* Luckily, TLAPS does not require us to decompose the proof into substeps. 
LEMMA TypeCorrect == Spec => []TypeInv
<1> USE Assumption DEF TypeInv
<1>1. Init => TypeInv BY SMT DEF Init
<1>2. TypeInv /\ [Next]_vars => TypeInv' BY SMT DEF Next, Put, Get, Wait, NotifyOther, vars
<1>. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM DeadlockFreedom == Spec => []Invariant
<1> USE Assumption, TypeCorrect DEF IInv, Invariant
<1>1. Init => IInv BY DEF Init
<1>2. TypeInv /\ IInv /\ [Next]_vars => IInv' BY DEF TypeInv, Next, Put, Get, Wait, NotifyOther, vars
<1>3. IInv => Invariant OBVIOUS 
<1>4. QED BY <1>1,<1>2,<1>3,PTL DEF Spec

=============================================================================

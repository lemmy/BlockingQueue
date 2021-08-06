-------------------- MODULE BlockingQueuePoisonApple_stats -------------------
EXTENDS BlockingQueuePoisonApple, CSV, TLC, TLCExt, Integers, IOUtils

Max(a,b) ==
    IF a > b THEN a ELSE b

Min(a,b) ==
    IF a < b THEN a ELSE b

-----------------------------------------------------------------------------

\* Collecting statistics does not work with an ordinary TLA+ spec such as 
\* BlockingQueuePoisonApple because of its non-determinism.  The statistics
\* would be all over the board and not meaningful.  Instead, we break the
\* non-determinism by mimiking a real-world workload s.t. each Producer adds
\* a (fixed) number of elements to the queue.  In other words, we remove 
\* those behaviors from the state space that we do not expect to see in the
\* executions of an implementation of the TLA+ spec.
\* It would be more convenient to conjoin a liveness property that stipulates
\* that each producer adds N elements to the queue instead of amending the
\* original next-state relation  Next  with  SNext  below.  However, I don't
\* see a way to get around adding the (auxiliary) pending variable that keeps
\* track of the number of elements added by each producer. 
\* Alternatively, a more variable approach, compared to producers adding a
\* fixed number of elements to the queue, would be to add probabilities that
\* model the likelyhood of a   Put  and  Terminate  actions to occur (with  
\*  Put  having a much higher probability).  This is straighforward to model
\* with TLC's  RandomElement  operator by conjoining it to  Put  and
\*  Terminate:
\*   RandomElement(1..10) \in 1..9
\* and
\*   RandomElement(1..10) \in 10..10
\* A more sophisticated example is at
\* https://github.com/lemmy/PageQueue/blob/master/PageQueue.tla

\* Number of elements to put into the queue by each producer.
CONSTANT Work
ASSUME Work \in (Nat \ {0})

\* Count how many elements have been added by each producer. This variable
\* is how we model workloads.
VARIABLES pending
auxVars == <<pending>>

\* The two auxilary variables are used to measure the over- and under-provisioning
\* of consumers.
\* TODO: Make Welford's algorithm for variance and standard deviation available
\*       here (https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_online_algorithm)
\*       It would free users from doing things in R, ... , and probably be useful
\*       in 99% of collecting statistics.
VARIABLE over, under
statsVars == <<over, under>>

STypeInv == 
    /\ pending \in [ Producers -> 0..Work ]
    /\ over \in Int
    /\ under \in Int

SInit == 
    \* Verbatim copy (redundant) of the original spec.
    /\ buffer = <<>>
    /\ waitSet = {}
    /\ cons = [ c \in Consumers |-> Cardinality(Producers) ]
    /\ prod = [ p \in Producers |-> Cardinality(Consumers) ]
    \* Workload:
    /\ pending = [ p \in Producers |-> Work ]
    \* Statistics:
    /\ over = 0
    /\ under = 0

SNext == 
    /\ \/ \E p \in Producers: /\ Put(p, p)
                              \* Decrement pending iff the buffer changed.
                              /\ IF buffer # buffer'
                                 THEN pending' = [pending EXCEPT ![p]=@-1]
                                 ELSE UNCHANGED pending
       \/ \E c \in Consumers: /\ Get(c) 
                              /\ UNCHANGED pending
    \* Update the statistics.
    /\ over' = Max(over, Cardinality(ac) - Cardinality(ap))
    /\ under' = Min(under, Cardinality(ac) - Cardinality(ap))

StatsSpec ==
    SInit /\ [][SNext]_<<vars, auxVars, statsVars>>

-----------------------------------------------------------------------------

CONSTANT CSVFile

StatsInv ==
    \* Per-behavior stats written to CSVfile on global termination.  Global
    \* termination is defined by the union of the active producers and consumers
    \* being the empty set.
    /\ (ap \cup ac = {}) =>
            CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s",
            <<
                \* TLCGet("stats").traces equals the number of traces generated
                \* so far.  Thus, individual records in the CSV can be aggregated
                \* later.  TLCGet("level")  can be seen as the timestamp of the
                \* record. 
                TLCGet("stats").traces, TLCGet("level"),
                \* 
                Cardinality(Producers), Cardinality(Consumers), BufCapacity,
                \* ...the actual statistics.
                over, under
            >>, CSVFile)

-----------------------------------------------------------------------------

\* Below, we read the values from the OS environment and turn them into constants
\* of this spec.  The operators  s2n  and  SetOfNModelValues  should probably be
\* moved into IOUtils.

s2n(str) ==
    CHOOSE n \in 0..2^16: ToString(n) = str

SetOfNModelValues(lbl, N) ==
   { TLCModelValue(lbl \o ToString(i)) : i \in 1..N }

-----------------------------------------------------------------------------

B ==
    s2n(IOEnv.B)

P ==
   SetOfNModelValues("p", s2n(IOEnv.P))

C ==
   SetOfNModelValues("c", s2n(IOEnv.C))

W ==
    s2n(IOEnv.W)

Out ==
    IOEnv.Out

===========================================================================

--------------------- CONFIG BlockingQueuePoisonApple_stats ---------------------
CONSTANTS
 BufCapacity <- B
 Producers   <- P
 Consumers   <- C
 Work        <- W
 CSVFile     <- Out
 Poison = Poison

SPECIFICATION StatsSpec

CHECK_DEADLOCK FALSE

INVARIANT STypeInv

INVARIANT StatsInv

=============================================================================

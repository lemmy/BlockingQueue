-------------------------- MODULE SimBlockingQueue --------------------------
EXTENDS BlockingQueue, CSV, SequencesExt, TLC

P ==
    SetToSeq(Producers)

C ==
    SetToSeq(Consumers)

SimInit == 
    /\ buffer = <<>>
    /\ waitSet = {}
    \* With the definition involving SUBSET in BlockingQueue!Init, the set of 
    \* initial states contains all combinations of producers and consumers.
    \* For example, for each producer p in the set of Producers, there is an
    \* initial state where producer = {p}.  This is not what we want because
    \* the length of the counterexample will be identicial.  Here, we just 
    \* choose one p (vice-versa for consumers) reducing the number of initial
    \* states to |Producers| * |Consumers| (ignoring the bufCapacity dimension
    \* in this calculation).  Welcome to poor-mans symmetry reduction.
    /\ \E p \in 1..Cardinality(Producers):
          /\ \E c \in 1..Cardinality(Consumers):
              /\ producers = ToSet(SubSeq(P, 1, p))
              /\ consumers = ToSet(SubSeq(C, 1, c))
    \* There is no point in checking larger values for bufCapacity because
    \* the system is deadlock-free if 2*bufCapacity >= |producers| + |consumers|.
    /\ bufCapacity \in 1..Cardinality(producers) + Cardinality(consumers)
    \*/\ PrintT(<<producers, consumers>>)

-----------------------------------------------------------------------------

CSVFile ==
    "R/SimBlockingQueue.csv"

(* No Deadlock *)
OnDeadlock == 
    (waitSet = (producers \cup consumers))
        => (/\ CSVWrite("%1$s#%2$s#%3$s#%4$s", 
                 <<bufCapacity, Cardinality(producers), Cardinality(consumers), TLCGet("level")>>,
                 CSVFile)
            /\ FALSE)

ASSUME
    CSVRecords(CSVFile) = 0 => CSVWrite("bufCapacity#producer#consumer#level", <<>>, CSVFile)

=============================================================================

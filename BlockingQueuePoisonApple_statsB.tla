---- MODULE BlockingQueuePoisonApple_statsB ----
EXTENDS TLC, TLCExt, IOUtils, Json, CSV, FiniteSets, Sequences, Integers

Max(a,b) ==
    IF a > b THEN a ELSE b

Min(a,b) ==
    IF a < b THEN a ELSE b

PowersOf2(n) ==
    {2^i : i \in 0..n}

---------------------------------------------------------------------------

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity, (* the maximum number of messages in the bounded buffer  *)
          Poison

VARIABLES B, P, C, buffer, waitSet, prod, cons

BQPA == INSTANCE BlockingQueuePoisonApple

---------------------------------------------------------------------------

\* The data collection below only works with TLC running in generation mode.
\* Unless TLC runs with -Dtlc2.tool.impl.Tool.probabilistic=true (or -generate).
\* the simulator generates all successor states and chooses one randomly. 
\* In "generate" mode, TLC randomly generates a (single) successor state.
\* Fail fast if TLC runs in modes that would cause bogus results.
ASSUME TLCGet("config").mode = "generate"

\* Prevent biasing the result by assuming that TLC is not limited to
\* too short behaviors.
ASSUME TLCGet("config").depth = -1

ToFile ==
    "BQPA_B_" \o ToString(JavaTime)

ASSUME JsonSerialize(ToFile \o ".json", <<TLCGet("config")>>)

CSVFile ==
    ToFile \o ".csv"

\* Write column headers at TLC startup.
ASSUME 
    CSVWrite("trace,level,P,C,B,over,under", <<>>, CSVFile)

BehaviorsTerminate ==
    \* Verify that the expected number of traces have been generated. Fewer
    \* traces indicate that some of the traces were longer than the value of
    \* TLC's -depth parameter. Semantically, this means those traces didn't
    \* terminate.
    TLCGet("config").traces = CSVRecords(CSVFile) - 1 \* Don't count the column header.

PlotStatistics ==
    \* Have TLC execute the R script on the generated CSV file.
    LET proc == IOExec(<<
            \* Find R on the current system (known to work on macOS and Linux).
            "/usr/bin/env", "Rscript",
            "BlockingQueuePoisonApple_statsB.R", CSVFile>>)
    IN \/ proc.exitValue = 0
       \/ PrintT(proc) \* Print stdout and stderr if R script fails.

PostConditions ==
    /\ BehaviorsTerminate
    /\ PlotStatistics

---------------------------------------------------------------------------

\* Up to N producers and consumers.
CONSTANT N

\* The two auxilary variables are used to measure the over- and under-provisioning
\* of consumers.
VARIABLE over, under

StatsInv ==
    \* Write stats on global termination.
    (BQPA!ap \cup BQPA!ac = {})
        =>
            CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s",
            <<
                TLCGet("stats").traces, TLCGet("level"),
                Cardinality(P), Cardinality(C), B,
                over, under
            >>, CSVFile)

GraphInv ==
    \* Periodically, have TLC regenerate the graph.
    (BQPA!ap \cup BQPA!ac = {}) /\ (TLCGet("stats").traces % 10 = 0)
        => PlotStatistics

---------------------------------------------------------------------------

InitStats == 
    /\ buffer = <<>>
    /\ waitSet = {}
    /\ P \in Producers
    /\ C \in Consumers
    \* Explore for symmetric in |P| and |C| configurations.
    /\ Cardinality(C) = Cardinality(P)
    /\ cons = [ c \in C |-> Cardinality(P) ]
    /\ prod = [ p \in P |-> Cardinality(C) ]
    /\ B \in N
    /\ over = 0
    /\ under = 0

Spec == 
    /\ InitStats
    /\ [][
            /\ over' = Max(over, Cardinality(BQPA!ac) - Cardinality(BQPA!ap))
            /\ under' = Min(under, Cardinality(BQPA!ac) - Cardinality(BQPA!ap))
            /\ BQPA!Next
        ]_<<over, under, BQPA!vars>>

---------------------------------------------------------------------------

LOCAL SetOfModelValues(lbl, n) == 
    { TLCModelValue(lbl \o ToString(i)) : i \in 1..n }

ProducerMV ==
    (* A typed set of model values for producers. *)
    { SetOfModelValues("p", n) : n \in N }

ConsumerMV ==
    (* A typed set of model values for consumers. *)
    { SetOfModelValues("c", n) : n \in N }

UpTo256 ==
    PowersOf2(8)
        
===========================================================================

---- CONFIG BlockingQueuePoisonApple_statsB ----

CONSTANTS
    N <- UpTo256
    BufCapacity = 128
    Producers <- ProducerMV
    Consumers <- ConsumerMV
    Poison = Poison

SPECIFICATION Spec
CHECK_DEADLOCK FALSE
INVARIANT StatsInv
INVARIANT GraphInv
POSTCONDITION PostConditions
====
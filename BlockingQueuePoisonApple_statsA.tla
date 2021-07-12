---- MODULE BlockingQueuePoisonApple_statsA ----
EXTENDS TLC, IOUtils, CSV, FiniteSets, Sequences, Naturals

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity, (* the maximum number of messages in the bounded buffer  *)
          Poison

VARIABLES B, P, C, buffer, waitSet, prod, cons

BQPA == INSTANCE BlockingQueuePoisonApple

---------------------------------------------------------------------------

(*************************************************)
(* Initialization of TLC and OS (constant-level) *)
(*************************************************)

\* The data collection below only works with TLC running in generation mode.
\* Unless TLC runs with -Dtlc2.tool.impl.Tool.probabilistic=true (or -generate).
\* the simulator generates all successor states and chooses one randomly. 
\* In "generate" mode, TLC randomly generates a (single) successor state.
\* Fail fast if TLC runs in modes that would cause bogus results.
ASSUME TLCGet("config").mode = "generate"

ToFile ==
    "BQPA_A_" \o ToString(JavaTime) \o ".csv"

\* Empty/clear any old ToFile at TLC startup and write column headers.
ASSUME 
    IOExec(
        <<"bash", "-c", 
            "echo \"trace#level#P#C#B#ap#ac\" > " \o ToFile>>
        ).exitValue = 0 \* Fail fast if ToFile was not created.

---------------------------------------------------------------------------

\* Conjoin with Next.
StatsNext == 
    CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s",
        <<
            \* In generation mode, TLCGet("diameter") returns the number of
            \* traces generated. Thus, it can be used to assign a unique
            \* identifier to each recorded trace.
            \* TODO How to deal with multiple workers reporting statistics
            \* TODO simultanously? Each data point would have to be assoicated
            \* TODO with the worker it was generated/reported by.  TLCGet("diameter")
            \* TODO is not the right way to do this because it is the diameter
            \* TODO of each individual worker.
            TLCGet("diameter"), 
            TLCGet("level"),
            Cardinality(P), Cardinality(C), B,
            Cardinality(BQPA!ap), Cardinality(BQPA!ac)
        >>, ToFile)    

\* Stats  is conjoined with  BQPA!Next  to ensure that stats are reported when
\* the next-state relation is evaluated. If  Stats  would be evaluated in a 
\* (state or action) constraint, it would be evaluated for all initial states.
Spec == 
    /\ BQPA!Init
    /\ [][
            /\ StatsNext
            /\ BQPA!Next
        ]_BQPA!vars

===========================================================================

---- CONFIG BlockingQueuePoisonApple_statsA ----

CONSTANTS
    BufCapacity = 20
    Producers = {p1,p2,p3,p4,p5,p6,p7,p8,p9}
    Consumers = {c1,c2,c3,c4,c5,c6,c7,c8,c9}
    Poison = Poison

SPECIFICATION Spec

====
Run on the command line as:

 $ alias tlcrepl
 alias tlcrepl='java -cp /opt/toolbox/CommunityModules-deps.jar:/opt/toolbox/tla2tools.jar tlc2.REPL'

 # Check all permutations of P, C, and B for the values {1,2,3,4}.
 $ tlcrepl 'LET TLC==<<"java", "-jar", "/opt/toolbox/tla2tools.jar",
                    "-config", "BlockingQueueStats.tla",
                    "-workers", "1", "-noTE", "-generate", "num=10",
                    "BlockingQueueStats">>
            IN { <<Conf, IOEnvExec(Conf, TLC).exitValue>> :
                        Conf \in [P: 1..4, C: 1..4, B: 1..1, F: {"na","no"}] }'

---------------------- MODULE BlockingQueueStats ---------------------------
EXTENDS BlockingQueue, IOUtils, TLC, TLCExt, Functions, CSV

B ==
    atoi(IOEnv.B)

SetOfNModelValues(lbl, N) ==
    { TLCModelValue(lbl \o ToString(i)) : i \in 1..N }

P ==
    SetOfNModelValues("p", atoi(IOEnv.P))

C ==
    SetOfNModelValues("c", atoi(IOEnv.C))

F ==
    IOEnv.F

-----------------------------------------------------------------------------

CSVFile ==
    "output.csv"
\*    "P" \o IOEnv.P \o "_C" \o IOEnv.C \o "_B" \o IOEnv.B \o ".csv"

ASSUME
    CSVRecords(CSVFile) = 0 => 
        CSVWrite("F#P#C#B#Level#WaitSet#Busy#EC#clicks#worked", <<>>, CSVFile)

Statistics ==
    CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s#%9$s#%10$s",
        <<F, Cardinality(P), Cardinality(C), B, 
            TLCGet("level"), Cardinality(waitSet), 
            Cardinality(busy),
            \*Cardinality({ p \in Producers: ENABLED Put(p,p) }),
            0,\*Cardinality({ c \in Consumers: ENABLED Get(c) }),
            TLCGet(clicks), TLCGet(worked)
        >>, CSVFile)

=============================================================================
------------------------ CONFIG BlockingQueueStats --------------------------
CONSTANTS
 BufCapacity <- B
 Producers <- P
 Consumers <- C
 Feature <- F

SPECIFICATION Spec

\* Statistics has to be an invariant because invariants are the only properties
\* that TLC only evaluates on distinct states.  If Statistics was a conjunct of
\* the next-state relation, TLC would evaluate it on all *generated* states
\* (except init states). The same problem is true for state- and
\* action-constraints; they are evaluated on all *generated* states.
INVARIANT Statistics

POSTCONDITION
    PostCondition

CHECK_DEADLOCK FALSE
=============================================================================

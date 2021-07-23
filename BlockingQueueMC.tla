Run on the command line as:

 $ alias tlcrepl
 alias tlcrepl='java -cp /opt/toolbox/CommunityModules-deps.jar:/opt/toolbox/tla2tools.jar tlc2.REPL'

 # Check all permutations of P, C, and B for the values {1,2,3,4}.
 $ tlcrepl 'LET TLC==<<"java", "-jar", "/opt/toolbox/tla2tools.jar", 
                    "-config", "BlockingQueueMC.tla",
                    "-workers", "auto", "-noTE", "BlockingQueueMC">>
            IN { <<Conf, IOEnvExec(Conf, TLC).exitValue>> : 
                        Conf \in [ {"P","C","B"} -> 1..4 ] }'

--------------------- MODULE BlockingQueueMC ---------------------
EXTENDS BlockingQueue, IOUtils, TLC, TLCExt

B ==
    atoi(IOEnv.B)

SetOfNModelValues(lbl, N) ==
    \* A set of N model values.
    { TLCModelValue(lbl \o ToString(i)) : i \in 1..N }

P ==
    \* A set of P producers (model values) where P is read from the 
    \* environment variable P.
    SetOfNModelValues("p", atoi(IOEnv.P))

C ==
    SetOfNModelValues("c", atoi(IOEnv.C))

=============================================================================
--------------------------- CONFIG BlockingQueueMC --------------------------
CONSTANTS
 BufCapacity <- B
 Producers <- P
 Consumers <- C

SPECIFICATION FairSpec

INVARIANT Invariant
INVARIANT TypeInv

PROPERTY Starvation

CHECK_DEADLOCK FALSE
=============================================================================

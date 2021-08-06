--------------------- MODULE BlockingQueuePoisonApple_statsSC ---------------------
EXTENDS TLC, IOUtils, Naturals, Sequences, CSV

\* Assume a recent version of TLC that has support for all shenanigans below.
ASSUME TLCGet("revision").timestamp >= 1628118195

-----------------------------------------------------------------------------

\* Filename for the CSV file that appears also in the R script and is passed
\* to the nested TLC instances that are forked below.
CSVFile ==
    "BQPA_B_" \o ToString(JavaTime) \o ".csv"

\* Write column headers to CSV file at startup of TLC instance that "runs"
\* this script and forks the nested instances of TLC that simulate the spec
\* and collect the statistics.
ASSUME 
    CSVWrite("trace,level,P,C,B,over,under", <<>>, CSVFile)

PlotStatistics ==
    \* Have TLC execute the R script on the generated CSV file.
    LET proc == IOExec(<<
            \* Find R on the current system (known to work on macOS and Linux).
            "/usr/bin/env", "Rscript",
            "BlockingQueuePoisonApple_stats.R", CSVFile>>)
    IN \/ proc.exitValue = 0
       \/ PrintT(proc) \* Print stdout and stderr if R script fails.

-----------------------------------------------------------------------------

\* Command to fork nested TLC instances that simulate the spec and collect the
\* statistics. TLCGet("config").install gives the path to the TLC jar also
\* running this script.
Cmd == LET absolutePathOfTLC == TLCGet("config").install
       IN <<"java", "-jar",
          absolutePathOfTLC, 
          "-generate", "num=100",
          "-config", "BlockingQueuePoisonApple_stats.tla",
          "BlockingQueuePoisonApple_stats">>

Success(e) ==
    /\ PrintT(e)
    /\ PlotStatistics

ASSUME \A conf \in 
            { r \in [ {"P","C","B"} -> {1,2,4,8,16,32}]:
                \* Check only symmetric configs of Producers and Consumers.
                \* Over/Under-provisioning for asymmetrics numbers of
                \*  Producers  and  Consumers.
                r.P = r.C }:
    LET ret == IOEnvExec(conf @@ [W |-> 16, Out |-> CSVFile], Cmd).exitValue
    IN CASE ret =  0 -> Success(conf)
         [] ret = 10 -> PrintT(<<conf, "Assumption violation">>)
         [] ret = 12 -> PrintT(<<conf, "Safety violation">>)
         [] ret = 13 -> PrintT(<<conf, "Liveness violation">>)
         [] OTHER    -> Print(<<conf, IOEnvExec(conf, Cmd), "Error">>, FALSE)

=============================================================================
---- CONFIG BlockingQueuePoisonAppleSC ----
\* TLC always expects a configuration file, but an empty one will do in this case.
\* If this approach proves useful, TLC should be extended to launch without a config
\* file.
====

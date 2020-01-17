------------------------- MODULE BlockingQueueDebug -------------------------
EXTENDS BlockingQueue, 
        TLC
        
DelayedNext == TLCSet("pause", TRUE) /\ Next

=============================================================================

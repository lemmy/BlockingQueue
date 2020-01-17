------------------------- MODULE BlockingQueueDebug -------------------------
EXTENDS BlockingQueue, 
        TLC,
        TLCExt \* Download https://github.com/tlaplus/CommunityModules/releases/download/20200107.1/CommunityModules-202001070430.jar

DelayedNext == TLCSet("pause", TRUE) /\ Next

(* 
  Note the primed waitSet variable through which we cause the "debugger" to
  break when the next-state's waitSet = Producers \cup Consumers. When the
  debugger halts, we can (interactively) skip/ignore the (successor) state
  that is a deadlock state.
 *)
NoDeadLock == PickSuccessor(waitSet' # (Producers \cup Consumers))

=============================================================================

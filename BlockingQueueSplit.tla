------------------------- MODULE BlockingQueueSplit -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSetC, waitSetP
vars == <<buffer, waitSetC, waitSetP>>

RunningThreads == (Producers \cup Consumers) \ (waitSetC \cup waitSetP)

NotifyOther(ws) == 
         \/ /\ ws = {}
            /\ UNCHANGED ws
         \/ /\ ws # {}
            /\ \E x \in ws: ws' = ws \ {x}

(* @see java.lang.Object#wait *)
Wait(ws, t) == /\ ws' = ws \cup {t}
               /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin waitSetP
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(waitSetC)
      /\ UNCHANGED waitSetP
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(waitSetP, t)
      /\ UNCHANGED waitSetC
      
Get(t) ==
/\ t \notin waitSetC
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(waitSetP)
      /\ UNCHANGED waitSetC
   \/ /\ buffer = <<>>
      /\ Wait(waitSetC, t)
      /\ UNCHANGED waitSetP

-----------------------------------------------------------------------------

TypeInv == /\ Len(buffer) \in 0..BufCapacity
           /\ waitSetP \in SUBSET Producers
           /\ waitSetC \in SUBSET Consumers

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSetC = {}
        /\ waitSetP = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars

=============================================================================

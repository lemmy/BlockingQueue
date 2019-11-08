--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity > 0                     (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet, consumers
vars == <<buffer, waitSet, consumers>>

RunningThreads == (Producers \cup consumers) \ waitSet

NotifyOther(t) == 
          LET S == IF t \in Producers THEN waitSet \ Producers ELSE waitSet \ consumers
          IN IF S # {}
             THEN \E x \in S : waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
   \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(t)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
   \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(t)
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}
        /\ consumers = Consumers

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == /\ \E t \in RunningThreads: \/ /\ t \in Producers
                                       /\ Put(t, t) \* Add some data to buffer
                                    \/ /\ t \in consumers
                                       /\ Get(t)
        \* Crash/Fail-stop semantics for consumers. Non-deterministically
        \* crash a subset of the consumers, but not all at once.
        /\ consumers' \in (SUBSET Consumers) \ {Consumers, consumers, {}}

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \subseteq (Producers \cup consumers)

(* No Deadlock *)
Invariant == waitSet # (Producers \cup consumers)

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* All producers will continuously be serviced. *)
ASSUME Cardinality(Producers) > 1 \* Mental note that starvation requires two or more producers.
Starvation == \A p \in Producers: []<>(<<Put(p, p)>>_vars)

=============================================================================

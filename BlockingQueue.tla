--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity, (* the maximum number of messages in the bounded buffer  *)
          Data

ASSUME /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity > 0                     (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet, thread
vars == <<buffer, waitSet, thread>>

RunningThreads == (Producers \cup Consumers) \ waitSet

(* @see java.lang.Object#notify *)       
Notify == IF waitSet # {}
          THEN \E x \in waitSet: waitSet' = waitSet \ {x}
          ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
   \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ Notify
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
   \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ Notify
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<"T","L","A","+">>
        /\ waitSet = {}
        /\ thread \in (Producers \cup Consumers)

(* Then, pick a thread out of all running threads and have it do its thing. *)
\* Next rewritten to predict the value of a prophecy variable
\* http://lamport.azurewebsites.net/pubs/auxiliary.pdf
\* (https://github.com/lorin/tla-prophecy)
Next == \/ /\ thread \notin waitSet                        \* Pred_A(i)
           /\ thread' \in (Producers \cup Consumers)       \* Setp
           /\ \/ /\ thread \in Producers                   \* A
                 /\ \E d \in Data: Put(thread, d) \* Add some data to buffer
              \/ /\ thread \in Consumers
                 /\ Get(thread)
        \/ /\ thread \in waitSet
           /\ UNCHANGED vars

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \subseteq (Producers \cup Consumers)

(* No Deadlock *)
Invariant == buffer # <<"C","O","N","F">> \* => waitSet # (Producers \cup Consumers)

=============================================================================



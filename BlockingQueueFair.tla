------------------------- MODULE BlockingQueueFair -------------------------
EXTENDS Naturals, Sequences, FiniteSets, Functions, SequencesExt

CONSTANTS 
    \* @type: Set(Str);
    Producers,   (* the (nonempty) set of producers                       *)
    \* @type: Set(Str);
    Consumers,   (* the (nonempty) set of consumers                       *)
    \* @type: Int;
    BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ Consumers \intersect Producers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES 
    \* @type: Seq(Str);
    buffer,
    \* @type: Seq(Str);
    waitSeqC,
    \* @type: Seq(Str);
    waitSeqP

\* @type: <<Seq(Str), Seq(Str), Seq(Str)>>;
vars == <<buffer, waitSeqC, waitSeqP>>

SeqToFunction(seq) ==  [ x \in 1..Len(seq) |-> seq[x]] 

WaitingThreads == Range(SeqToFunction(waitSeqC)) \cup Range(SeqToFunction(waitSeqP))

RunningThreads == (Producers \cup Consumers) \ WaitingThreads

NotifyOther(ws) ==
            \/ /\ ws = <<>>
               /\ UNCHANGED ws
            \/ /\ ws # <<>>
               /\ ws' = Tail(ws)

(* @see java.lang.Object#wait *)
Wait(ws, t) == 
            /\ ws' = Append(ws, t)
            /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin Range(SeqToFunction(waitSeqP))
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(waitSeqC)
      /\ UNCHANGED waitSeqP
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(waitSeqP, t)
      /\ UNCHANGED waitSeqC
      
Get(t) ==
/\ t \notin Range(SeqToFunction(waitSeqC))
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(waitSeqP)
      /\ UNCHANGED waitSeqC
   \/ /\ buffer = <<>>
      /\ Wait(waitSeqC, t)
      /\ UNCHANGED waitSeqP

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars 

FairSpec == Spec /\ \A c \in Consumers : WF_vars(Get(c)) 
                 /\ \A p \in Producers : WF_vars(Put(p, p)) 

----------------

BQS == INSTANCE BlockingQueueSplit WITH waitSetC <- Range(SeqToFunction(waitSeqC)), 
                                        waitSetP <- Range(SeqToFunction(waitSeqP))

BQSSpec == BQS!Spec
SpecImpliesBQSSpec == Spec => BQSSpec

BQSFairSpec == BQS!A!FairSpec
FairSpecImpliesBQSFairSpec == FairSpec => BQSFairSpec

BQSStarvation == BQS!A!Starvation
FairSpecImpliesBQSStarvation == FairSpec => BQSStarvation
-----------------------------------------------------------------------------

TypeInv == /\ Len(buffer) \in 0..BufCapacity
           \* Producers
           /\ waitSeqP \in Seq(Producers)
           /\ IsInjective(SeqToFunction(waitSeqP)) \* no duplicates (thread is either asleep or not)!
           \* Consumers
           /\ waitSeqC \in Seq(Consumers)
           /\ IsInjective(SeqToFunction(waitSeqC)) \* no duplicates (thread is either asleep or not)!

=============================================================================

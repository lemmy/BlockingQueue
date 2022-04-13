------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

K == 3
P == {"p1", "p2", "p3", "p4"}
C == {"c1", "c2", "c3"}

(* --fair algorithm BlockingQueue {

    variable 
        queue = <<>>;

    define {
         isFull ==
             Len(queue) = K
         isEmpty == 
             Len(queue) = 0
    }

    macro wait() { 
        \* Instrinsic \*
        skip;
    }

    macro notify() {
        \* Instrinsic \*
        skip;
    }

    process (producer \in P) {
         put: while (TRUE) {
                  if (isFull) { 
                    wait();
                  } else { 
                    notify();
                    queue := Append(queue, self);
                  };
              };
    }

    process (consumer \in C) {
        take: while (TRUE) {
                 if (isEmpty) {
                    wait();
                 } else { 
                    notify();
                    queue := Tail(queue);
                 };
              };
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "ebdc58d3")
VARIABLE queue

(* define statement *)
isFull ==
    Len(queue) = K
isEmpty ==
    Len(queue) = 0


vars == << queue >>

ProcSet == (P) \cup (C)

Init == (* Global variables *)
        /\ queue = <<>>

producer(self) == IF isFull
                     THEN /\ TRUE
                          /\ queue' = queue
                     ELSE /\ TRUE
                          /\ queue' = Append(queue, self)

consumer(self) == IF isEmpty
                     THEN /\ TRUE
                          /\ queue' = queue
                     ELSE /\ TRUE
                          /\ queue' = Tail(queue)

Next == (\E self \in P: producer(self))
           \/ (\E self \in C: consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 
=============================================================================


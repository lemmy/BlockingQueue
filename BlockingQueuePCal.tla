------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

P == {"p1","p2","p3","p4"}
C == {"c1","c2","c3","c4"}
K == 3

(* --fair algorithm BlockingQueue {

    variable 
        queue = <<>>;
        waitset = {};

    define {
         isFull ==
             Len(queue) = K
         isEmpty == 
             Len(queue) = 0
        NeverDeadlock ==
            waitset # P \cup C
    }

    macro wait() { 
        \* Instrinsic \*
        waitset := waitset \union {self};
    }

    macro notify() {
        \* Instrinsic \*
        if (waitset # {}) {
            with (w \in waitset) {
                waitset := waitset \ {w};
            }
        }
    }

    macro notifyAll() {
        \* Instrinsic \*
        waitset := {};
    }

    macro notifyOther(O) {
        \* Instrinsic \*
        if (waitset # {} \cap O) {
            with (w \in waitset \cap O) {
                waitset := waitset \ {w};
            }
        }
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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "bb5b3f7a")
VARIABLES queue, waitset

(* define statement *)
 isFull ==
     Len(queue) = K
 isEmpty ==
     Len(queue) = 0
NeverDeadlock ==
    waitset # P \cup C


vars == << queue, waitset >>

ProcSet == (P) \cup (C)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ waitset = {}

producer(self) == IF isFull
                     THEN /\ waitset' = (waitset \union {self})
                          /\ queue' = queue
                     ELSE /\ IF waitset # {}
                                THEN /\ \E w \in waitset:
                                          waitset' = waitset \ {w}
                                ELSE /\ TRUE
                                     /\ UNCHANGED waitset
                          /\ queue' = Append(queue, self)

consumer(self) == IF isEmpty
                     THEN /\ waitset' = (waitset \union {self})
                          /\ queue' = queue
                     ELSE /\ IF waitset # {}
                                THEN /\ \E w \in waitset:
                                          waitset' = waitset \ {w}
                                ELSE /\ TRUE
                                     /\ UNCHANGED waitset
                          /\ queue' = Tail(queue)

Next == (\E self \in P: producer(self))
           \/ (\E self \in C: consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

NeverStarve ==
    \forall p \in P: []<>(<<producer(p)>>_vars)
=============================================================================


 ------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

K == 3
P == {"p1","p2","p3","p4"}
C == {"c1", "c2", "c3"}

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
            waitset # P \union C
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
        };
    }

    macro notifyOther(O) {
        \* Instrinsic \*
        if (waitset # {} \cap O) {
            with (w \in waitset \cap O) {
                waitset := waitset \ {w};
            }
        };
    }

    process (producer \in P) {
         put: while (TRUE) {
                  if (isFull) { 
                    wait();
                  } else { 
                    notifyOther(C);
                    queue := Append(queue, self);
                  };
              };
    }

    process (consumer \in C) {
        take: while (TRUE) {
                 if (isEmpty) {
                    wait();
                 } else { 
                    notifyOther(P);
                    queue := Tail(queue);
                 };
              };
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "ce51f923")
VARIABLES queue, waitset

(* define statement *)
 isFull ==
     Len(queue) = K
 isEmpty ==
     Len(queue) = 0
NeverDeadlock ==
    waitset # P \union C


vars == << queue, waitset >>

ProcSet == (P) \cup (C)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ waitset = {}

producer(self) == IF isFull
                     THEN /\ waitset' = (waitset \union {self})
                          /\ queue' = queue
                     ELSE /\ IF waitset # {} \cap C
                                THEN /\ \E w \in waitset \cap C:
                                          waitset' = waitset \ {w}
                                ELSE /\ TRUE
                                     /\ UNCHANGED waitset
                          /\ queue' = Append(queue, self)

consumer(self) == IF isEmpty
                     THEN /\ waitset' = (waitset \union {self})
                          /\ queue' = queue
                     ELSE /\ IF waitset # {} \cap P
                                THEN /\ \E w \in waitset \cap P:
                                          waitset' = waitset \ {w}
                                ELSE /\ TRUE
                                     /\ UNCHANGED waitset
                          /\ queue' = Tail(queue)

Next == (\E self \in P: producer(self))
           \/ (\E self \in C: consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

NoStarvation ==
    \forall p \in P: []<>(<<producer(p)>>_vars)
=============================================================================


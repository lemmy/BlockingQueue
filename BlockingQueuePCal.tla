 ------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

C == SUBSET {"c1", "c2", "c3", "c4"} \ {{}}
P == SUBSET {"p1", "p2", "p3", "p4"} \ {{}}
K == 1..4

(* --algorithm BlockingQueue {

    variable 
        store = <<>>;
        waitsetC = {};
        waitsetP = {};
        k \in K;
        c \in C;
        p \in P;

    define {
         isFull == Len(store) = k
         isEmpty == Len(store) = 0

         NoDeadlock == (waitsetC \cup waitsetP) # (c \cup p)
    }

    macro wait(WaitSet) { 
         WaitSet := WaitSet \cup {self}
    }

    macro notify(WaitSet) {
         if (WaitSet # {}) {
             with ( i \in WaitSet ) {
                 WaitSet := WaitSet \ {i};
             }
         }
    }

    process (producer \in (p \ waitsetP)) {
         put: while (TRUE) {
                  if (isFull) { 
                    wait(waitsetP);
                  } else { 
                    notify(waitsetC);
                    store := Append(store, self);
                  };
              };
    }

    process (consumer \in (c \ waitsetC)) {
        take: while (TRUE) {
                 if (isEmpty) {
                    wait(waitsetC);
                 } else { 
                    notify(waitsetP);
                    store := Tail(store);
                 };
              };
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "c78369b9" /\ chksum(tla) = "4525d6a")
VARIABLES store, waitsetC, waitsetP, k, c, p

(* define statement *)
isFull == Len(store) = k
isEmpty == Len(store) = 0

NoDeadlock == (waitsetC \cup waitsetP) # (c \cup p)


vars == << store, waitsetC, waitsetP, k, c, p >>

ProcSet == ((p \ waitsetP)) \cup ((c \ waitsetC))

Init == (* Global variables *)
        /\ store = <<>>
        /\ waitsetC = {}
        /\ waitsetP = {}
        /\ k \in K
        /\ c \in C
        /\ p \in P

producer(self) == /\ IF isFull
                        THEN /\ waitsetP' = (waitsetP \cup {self})
                             /\ UNCHANGED << store, waitsetC >>
                        ELSE /\ IF waitsetC # {}
                                   THEN /\ \E i \in waitsetC:
                                             waitsetC' = waitsetC \ {i}
                                   ELSE /\ TRUE
                                        /\ UNCHANGED waitsetC
                             /\ store' = Append(store, self)
                             /\ UNCHANGED waitsetP
                  /\ UNCHANGED << k, c, p >>

consumer(self) == /\ IF isEmpty
                        THEN /\ waitsetC' = (waitsetC \cup {self})
                             /\ UNCHANGED << store, waitsetP >>
                        ELSE /\ IF waitsetP # {}
                                   THEN /\ \E i \in waitsetP:
                                             waitsetP' = waitsetP \ {i}
                                   ELSE /\ TRUE
                                        /\ UNCHANGED waitsetP
                             /\ store' = Tail(store)
                             /\ UNCHANGED waitsetC
                  /\ UNCHANGED << k, c, p >>

Next == (\E self \in (p \ waitsetP): producer(self))
           \/ (\E self \in (c \ waitsetC): consumer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================


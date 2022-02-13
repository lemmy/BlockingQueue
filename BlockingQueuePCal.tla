 ------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

c == {"c1"}
p == {"p1", "p2"}
k == 1

(* --fair algorithm BlockingQueue {

    variable 
        store = <<>>;
        waitsetC = {};
        waitsetP = {};

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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "d1f78689")
VARIABLES store, waitsetC, waitsetP

(* define statement *)
isFull == Len(store) = k
isEmpty == Len(store) = 0

NoDeadlock == (waitsetC \cup waitsetP) # (c \cup p)


vars == << store, waitsetC, waitsetP >>

ProcSet == ((p \ waitsetP)) \cup ((c \ waitsetC))

Init == (* Global variables *)
        /\ store = <<>>
        /\ waitsetC = {}
        /\ waitsetP = {}

producer(self) == IF isFull
                     THEN /\ waitsetP' = (waitsetP \cup {self})
                          /\ UNCHANGED << store, waitsetC >>
                     ELSE /\ IF waitsetC # {}
                                THEN /\ \E i \in waitsetC:
                                          waitsetC' = waitsetC \ {i}
                                ELSE /\ TRUE
                                     /\ UNCHANGED waitsetC
                          /\ store' = Append(store, self)
                          /\ UNCHANGED waitsetP

consumer(self) == IF isEmpty
                     THEN /\ waitsetC' = (waitsetC \cup {self})
                          /\ UNCHANGED << store, waitsetP >>
                     ELSE /\ IF waitsetP # {}
                                THEN /\ \E i \in waitsetP:
                                          waitsetP' = waitsetP \ {i}
                                ELSE /\ TRUE
                                     /\ UNCHANGED waitsetP
                          /\ store' = Tail(store)
                          /\ UNCHANGED waitsetC

Next == (\E self \in (p \ waitsetP): producer(self))
           \/ (\E self \in (c \ waitsetC): consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

NoStarvation ==
    /\ \A cc \in c: []<>(<<consumer(cc)>>_vars)
    /\ \A pp \in p: []<>(<<producer(pp)>>_vars)

=============================================================================


 ------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

(* --algorithm BlockingQueue {

    variable 
        store = <<>>;
        waitset = {};
        k = 1;
        c = {"c1"};
        p = {"p1","p2"};

    define {
         isFull == Len(store) = k
         isEmpty == Len(store) = 0
    }

    macro wait() { 
         waitset := waitset \cup {self}
    }

    macro notify() {
         if (waitset # {}) {
             with ( i \in waitset ) {
                 waitset := waitset \ {i};
             }
         }
    }

    process (producer \in (p \ waitset)) {
         put: while (TRUE) {
                  if (isFull) { 
                    wait();
                  } else { 
                    notify();
                    store := Append(store, self);
                  };
              };
    }

    process (consumer \in (c \ waitset)) {
        take: while (TRUE) {
                 if (isEmpty) {
                    wait();
                 } else { 
                    notify();
                    store := Tail(store);
                 };
              };
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "e77de6b3" /\ chksum(tla) = "3c775ad7")
VARIABLES store, waitset, k, c, p

(* define statement *)
isFull == Len(store) = k
isEmpty == Len(store) = 0


vars == << store, waitset, k, c, p >>

ProcSet == ((p \ waitset)) \cup ((c \ waitset))

Init == (* Global variables *)
        /\ store = <<>>
        /\ waitset = {}
        /\ k = 1
        /\ c = {"c1"}
        /\ p = {"p1","p2"}

producer(self) == /\ IF isFull
                        THEN /\ waitset' = (waitset \cup {self})
                             /\ store' = store
                        ELSE /\ IF waitset # {}
                                   THEN /\ \E i \in waitset:
                                             waitset' = waitset \ {i}
                                   ELSE /\ TRUE
                                        /\ UNCHANGED waitset
                             /\ store' = Append(store, self)
                  /\ UNCHANGED << k, c, p >>

consumer(self) == /\ IF isEmpty
                        THEN /\ waitset' = (waitset \cup {self})
                             /\ store' = store
                        ELSE /\ IF waitset # {}
                                   THEN /\ \E i \in waitset:
                                             waitset' = waitset \ {i}
                                   ELSE /\ TRUE
                                        /\ UNCHANGED waitset
                             /\ store' = Tail(store)
                  /\ UNCHANGED << k, c, p >>

Next == (\E self \in (p \ waitset): producer(self))
           \/ (\E self \in (c \ waitset): consumer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================


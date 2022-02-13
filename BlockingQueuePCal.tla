 ------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

C == SUBSET {"c1", "c2", "c3", "c4"} \ {{}}
P == SUBSET {"p1", "p2", "p3", "p4"} \ {{}}
K == 1..4

(* --algorithm BlockingQueue {

    variable 
        store = <<>>;
        waitset = {};
        k \in K;
        c \in C;
        p \in P;

    define {
         isFull == Len(store) = k
         isEmpty == Len(store) = 0

         NoDeadlock == waitset # (c \cup p)
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

    macro notifyAll() {
         waitset := {};
    }

    process (producer \in (p \ waitset)) {
         put: while (TRUE) {
                  if (isFull) { 
                    wait();
                  } else { 
                    notifyAll();
                    store := Append(store, self);
                  };
              };
    }

    process (consumer \in (c \ waitset)) {
        take: while (TRUE) {
                 if (isEmpty) {
                    wait();
                 } else { 
                    notifyAll();
                    store := Tail(store);
                 };
              };
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "44354781" /\ chksum(tla) = "1de24380")
VARIABLES store, waitset, k, c, p

(* define statement *)
isFull == Len(store) = k
isEmpty == Len(store) = 0

NoDeadlock == waitset # (c \cup p)


vars == << store, waitset, k, c, p >>

ProcSet == ((p \ waitset)) \cup ((c \ waitset))

Init == (* Global variables *)
        /\ store = <<>>
        /\ waitset = {}
        /\ k \in K
        /\ c \in C
        /\ p \in P

producer(self) == /\ IF isFull
                        THEN /\ waitset' = (waitset \cup {self})
                             /\ store' = store
                        ELSE /\ waitset' = {}
                             /\ store' = Append(store, self)
                  /\ UNCHANGED << k, c, p >>

consumer(self) == /\ IF isEmpty
                        THEN /\ waitset' = (waitset \cup {self})
                             /\ store' = store
                        ELSE /\ waitset' = {}
                             /\ store' = Tail(store)
                  /\ UNCHANGED << k, c, p >>

Next == (\E self \in (p \ waitset): producer(self))
           \/ (\E self \in (c \ waitset): consumer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================


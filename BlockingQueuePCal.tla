 ------------------------- MODULE BlockingQueuePCal -------------------------
EXTENDS Integers, FiniteSets, Sequences

Range(f) ==
    { f[x] : x \in DOMAIN f}

c == {"c1"}
p == {"p1", "p2"}
k == 1

(* --algorithm BlockingQueue {

    variable 
        store = <<>>;
        waitseqC = <<>>;
        waitseqP = <<>>;

    define {
         isFull == Len(store) = k
         isEmpty == Len(store) = 0

         NoDeadlock == (Range(waitseqC) \cup Range(waitseqP)) # (c \cup p)
    }

    macro wait(WaitSeq) { 
         WaitSeq := WaitSeq \o <<self>>
    }

    macro notify(WaitSeq) {
         if (WaitSeq # <<>>) {
             WaitSeq := Tail(WaitSeq)
         }
    }

    fair process (producer \in p) {
         put: if (self \notin Range(waitseqP)) {
                  if (isFull) { 
                    wait(waitseqP);
                  } else { 
                    notify(waitseqC);
                    store := Append(store, self);
                  };
              };
              goto put;
    }

    fair process (consumer \in c) {
        take: if (self \notin Range(waitseqC)) {
                 if (isEmpty) {
                    wait(waitseqC);
                 } else { 
                    notify(waitseqP);
                    store := Tail(store);
                 };
              };
              goto take;
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "d753d008" /\ chksum(tla) = "5e1da1c7")
VARIABLES store, waitseqC, waitseqP, pc

(* define statement *)
isFull == Len(store) = k
isEmpty == Len(store) = 0

NoDeadlock == (Range(waitseqC) \cup Range(waitseqP)) # (c \cup p)


vars == << store, waitseqC, waitseqP, pc >>

ProcSet == (p) \cup (c)

Init == (* Global variables *)
        /\ store = <<>>
        /\ waitseqC = <<>>
        /\ waitseqP = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in p -> "put"
                                        [] self \in c -> "take"]

put(self) == /\ pc[self] = "put"
             /\ IF self \notin Range(waitseqP)
                   THEN /\ IF isFull
                              THEN /\ waitseqP' = waitseqP \o <<self>>
                                   /\ UNCHANGED << store, waitseqC >>
                              ELSE /\ IF waitseqC # <<>>
                                         THEN /\ waitseqC' = Tail(waitseqC)
                                         ELSE /\ TRUE
                                              /\ UNCHANGED waitseqC
                                   /\ store' = Append(store, self)
                                   /\ UNCHANGED waitseqP
                   ELSE /\ TRUE
                        /\ UNCHANGED << store, waitseqC, waitseqP >>
             /\ pc' = [pc EXCEPT ![self] = "put"]

producer(self) == put(self)

take(self) == /\ pc[self] = "take"
              /\ IF self \notin Range(waitseqC)
                    THEN /\ IF isEmpty
                               THEN /\ waitseqC' = waitseqC \o <<self>>
                                    /\ UNCHANGED << store, waitseqP >>
                               ELSE /\ IF waitseqP # <<>>
                                          THEN /\ waitseqP' = Tail(waitseqP)
                                          ELSE /\ TRUE
                                               /\ UNCHANGED waitseqP
                                    /\ store' = Tail(store)
                                    /\ UNCHANGED waitseqC
                    ELSE /\ TRUE
                         /\ UNCHANGED << store, waitseqC, waitseqP >>
              /\ pc' = [pc EXCEPT ![self] = "take"]

consumer(self) == take(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in p: producer(self))
           \/ (\E self \in c: consumer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in p : WF_vars(producer(self))
        /\ \A self \in c : WF_vars(consumer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

NoStarvation ==
    /\ \A cc \in c: []<>(<<consumer(cc)>>_vars)
    /\ \A pp \in p: []<>(<<producer(pp)>>_vars)

=============================================================================


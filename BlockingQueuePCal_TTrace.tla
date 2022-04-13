---- MODULE BlockingQueuePCal_TTrace ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, BlockingQueuePCal, TTrace

_expression ==
    LET BlockingQueuePCal_TEExpression == INSTANCE BlockingQueuePCal_TEExpression
    IN BlockingQueuePCal_TEExpression!expression
----

_trace(i) ==
    LET BlockingQueuePCal_TETrace(_index) == INSTANCE BlockingQueuePCal_TETrace
    IN BlockingQueuePCal_TETrace(i)!trace
----

VARIABLE _index

_inv ==
    ~(
        TLCGet("level") = Len(_trace(_index))
        /\
        waitset = (_trace(_index)[Len(_trace(_index))].waitset)
        /\
        queue = (_trace(_index)[Len(_trace(_index))].queue)
    )
----

_init ==
    /\ _index \in 1..2
    /\ waitset = _trace(_index)[1].waitset
    /\ queue = _trace(_index)[1].queue

----

_next ==
    /\ UNCHANGED _index
    /\ \E i,j \in DOMAIN _trace(_index):
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ waitset  = _trace(_index)[i].waitset
        /\ waitset' = _trace(_index)[j].waitset
        /\ queue  = _trace(_index)[i].queue
        /\ queue' = _trace(_index)[j].queue

_view == _View(<<vars, _index>>, _trace(_index))

BQP == INSTANCE BlockingQueuePCal

\* Assert that the high-level spec's config matches the one of this trace.
\* In a more real-world example, P/C/K would likely be CONSTANTS, which
\* we could then rather include in a refinement mapping.
ASSUME /\ BQP!P = {"p1","p2","p3","p4"}
       /\ BQP!C = {"c1","c2","c3","c4"}
       /\ BQP!K = 3

\* A possible fairness constraint of BQP!Spec would get in our way when checking the trace,
\* because TLC would report stuttering after the initial state (trace spec has no fairness).
\* Thus, we redefine Spec here without a fairness constraint.
BQPSpec == BQP!Init /\ [][BQP!Next]_BQP!vars

\* TLC rejects the following with: Error: Temporal formulas containing actions must be of forms <>[]A or []<>A.
\* _implements == 
\*     LET HL == INSTANCE BlockingQueuePCal
\*     IN HL!Init /\ [][HL!Next]_HL!vars

=============================================================================

---- MODULE BlockingQueuePCal_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, BlockingQueuePCal

expression == 
    [
        waitset |-> waitset
        ,queue |-> queue
    ]

=============================================================================

---- MODULE BlockingQueuePCal_TETrace ----
EXTENDS TLC, BlockingQueuePCal

VARIABLE _index

_trace ==
    <<
        <<
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {"c2"},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p3">>]),
        ([waitset |-> {},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {"c2"},queue |-> <<>>]),
        ([waitset |-> {"c2", "c3"},queue |-> <<>>]),
        ([waitset |-> {"c2"},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p1">>]),
        ([waitset |-> {},queue |-> <<"p1">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {"c3"},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p2">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p2">>]),
        ([waitset |-> {},queue |-> <<"p2", "p1">>]),
        ([waitset |-> {},queue |-> <<"p1">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {"c1"},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {"c1"},queue |-> <<>>]),
        ([waitset |-> {"c1", "c3"},queue |-> <<>>]),
        ([waitset |-> {"c1", "c3"},queue |-> <<>>]),
        ([waitset |-> {"c1", "c3"},queue |-> <<>>]),
        ([waitset |-> {"c3"},queue |-> <<"p2">>]),
        ([waitset |-> {},queue |-> <<"p2", "p3">>]),
        ([waitset |-> {},queue |-> <<"p2", "p3", "p3">>]),
        ([waitset |-> {"p2"},queue |-> <<"p2", "p3", "p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p3", "p3">>]),
        ([waitset |-> {"p3"},queue |-> <<"p3", "p3", "p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p3", "p2">>]),
        ([waitset |-> {"p2"},queue |-> <<"p3", "p3", "p2">>]),
        ([waitset |-> {"p2"},queue |-> <<"p3", "p3", "p2">>]),
        ([waitset |-> {"p1", "p2"},queue |-> <<"p3", "p3", "p2">>]),
        ([waitset |-> {"p1", "p2"},queue |-> <<"p3", "p3", "p2">>]),
        ([waitset |-> {"p1", "p2"},queue |-> <<"p3", "p3", "p2">>]),
        ([waitset |-> {"p2"},queue |-> <<"p3", "p2">>]),
        ([waitset |-> {},queue |-> <<"p3", "p2", "p2">>]),
        ([waitset |-> {"p3"},queue |-> <<"p3", "p2", "p2">>]),
        ([waitset |-> {},queue |-> <<"p2", "p2">>]),
        ([waitset |-> {},queue |-> <<"p2">>]),
        ([waitset |-> {},queue |-> <<"p2", "p3">>]),
        ([waitset |-> {},queue |-> <<"p3">>])
        >>,
        <<
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p1">>]),
        ([waitset |-> {},queue |-> <<"p3", "p1", "p2">>]),
        ([waitset |-> {},queue |-> <<"p1", "p2">>]),
        ([waitset |-> {},queue |-> <<"p2">>]),
        ([waitset |-> {},queue |-> <<>>]),
        ([waitset |-> {},queue |-> <<"p3">>]),
        ([waitset |-> {},queue |-> <<"p3", "p1">>]),
        ([waitset |-> {},queue |-> <<"p3", "p1", "p2">>]),
        ([waitset |-> {},queue |-> <<"p1", "p2">>]),
        ([waitset |-> {},queue |-> <<"p2">>]),
        ([waitset |-> {},queue |-> <<>>])
        >>
    >>
----

trace == 
    _trace[_index]

=============================================================================

---- MODULE TTrace ----

EXTENDS BlockingQueuePCal, Toolbox, TLC


_View(vrs, trc) ==
    LET NoLassoOrFiniteStuttering ==
        \* TODO: With long traces of involved states, this will be too costly
        \* TODO: (if evaluated over and over again)!
        Cardinality({ trc[i] : i \in 1..Len(trc) }) = Len(trc)
    IN
    \* If the behavior has been generated with the simulator or manually, a
    \* state or states can appear multiple times (beyond inifite stuttering).
    \* after the last state). In this case, TLC's BFS is "too smart" and stops
    \* at the first state that is a repetition.  With this view definition,
    \* we guarantee that all states are explored.
    \* Note, though, that this approach does *not* work if the next-state relation
    \* is the original one of the system spec.  The generated next-state relation
    \* _next has to be configured as NEXT in TLC's config file.
    \* Note that we do not include a counter variable in the generated spec
    \* to guarantee that violations that end in stuttering are re-creatable.
    \* TODO Consider conditionally including TLCGet for as long as TLCGet("level") < Len(trc).
    IF NoLassoOrFiniteStuttering
    THEN vrs
    ELSE <<vrs, TLCGet("level")>>

--------

PostCond ==
    \* TLCGet("diameter") doesn't work with a lasso because TLC skips the lasso state in BFS mode.
    \* However, activating _view above would work around this problem.
    \* TLCGet("diameter") = Len(_TETrace)

    \* TLCGet("distinct") doesn't work for the same reason that "diameter" doesn't work.
    \* TLCGet("distinct") = Len(_TETrace)

    \* TLCGet("generated") is pretty unreliable and unpredictable because it depends on TLC internals.
    \* TLCGet("generated") = Len(_TETrace)

    \* TLCGet("level") = 0 when evaluating the postcondition.

    \* TLCGet(23) = Len(_TETrace) with TLCSet/Get appearing in _init and _next works iff _next is 
    \* the next-state relation (NEXT), and not an ACTION_CONSTRAINT with the original Next as NEXT
    \* (that gives us proper action names).  With the original Next as NEXT, TLCGet(23) >= Len(_TETrace)
    \* because TLC evaluates _next multiple times.
    \* /\ Print(<<TLCGet(23), Len(_TETrace)>>, TLCGet(23) = Len(_TETrace))

    /\ Print(<<TLCGet("distinct"), Len(_TETrace)>>, TLCGet("distinct") = Len(_TETrace))

_live ==
    \* Introducing an artificial counter variable effectively changes the behavior s.t.
    \* the counter can increment even if the spec vars don't.  Could potentiall work
    \* around this problem by carefully crafting the subscript of the behavior spec.

    \* By the way, generating a universially correct behavior spec is difficult.
    \* A liveness property has the disadvantage that it requires a fairness
    \* constraint, which is not directly supported because we don't generate
    \* a behavior spec (_spec) formula such as:
    \* _spec == _init /\ [][_next]_vars /\ WF_vars(_next)
    \* Also, the fairness constraint (conjunct) might actually involve many sub-actions;
    \* not just Next.

    \* Cannot use eventually neg _inv because the state defined by _inv
    \* might occur in the behavior multiple times (think lasso)
    \* <>~_inv

    \* <>(TLCGet("level") = Len(_TETrace)) does not work because TLCGet("level")
    \* cannot be evaluated by liveness checking, and again require a fairness
    \* constraint.
    \* <>(TLCGet("level") = Len(_TETrace)) 

    FALSE

======

\* Write a test script that asserts that the spec violates the properties.
\* https://github.com/tlaplus/azure-cosmos-tla/blob/master/.github/Regressions.tla
\* This idea needs better tooling because it is too cumbersome right now. 

---- CONFIG BlockingQueuePCal_TTrace ----

\* INVARIANT
\*     _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
\*     Next

\* ACTION_CONSTRAINT
    _next

\* CONSTANT
\*     _TETrace <- _trace

ALIAS
    _expression

VIEW
    _view

\* Commented because TTRace!PostCondition uses _TETrace instead of _trace.
\* POSTCONDITION
\*     PostCond

PROPERTY
    BQPSpec
=============================================================================
\* Generated on Thu Apr 07 17:35:49 PDT 2022
------------------------- MODULE BlockingQueueAnim -------------------------
EXTENDS SVG, SequencesExt, Toolbox, BlockingQueue

---------------------------------------------------------------------------
(*
  The operators up here connect the presentation below to the states in
  the error trace.  In Model-View-Control terms, this would be the control,
  the error trace is the model, and the layout description at the end of
  this file is the view).
*)

Null == ""

\* Don't ToString("") to avoid ugly \"\" from being printed. TLC's ToString
\* should probably be smarter about this. 
ToStringNull(e) == IF e = Null THEN "" ELSE ToString(e)

\* The element of (S1 \ S2) or Null if (S1 \ S2) = {}.
\* Assumes Cardinality(S1 \ S2) <= 1.
\* Guard against choosing from {}.
Diff(S1, S2) == 
  CASE S1 \ S2 # {} -> CHOOSE e \in (S1 \ S2) : TRUE
           [] OTHER -> Null

-------------------------------------------------------------------------

\* Just short-hands.
curBuf == _TETrace[_TEPosition].buffer

Waiting == _TETrace[_TEPosition].waitSet
Running == (Producers \cup Consumers) \ Waiting 

Scheduled == _TETrace[_TEPosition].thread

\* The element of buffer at index i or Null if i is out-of-bounds.
ElemAt(i) == IF i > Len(curBuf)
             THEN Null
             ELSE curBuf[i]

\* Problem: The following is clumsy, primarily because it has to check if 
\* _TETrace is out-of-bounds

nxtBuf == IF _TEPosition < Len(_TETrace)
          THEN _TETrace[_TEPosition + 1].buffer
          ELSE << >> \* No next buffer after last state of the trace.

prvBuf == IF _TEPosition > 1
          THEN _TETrace[_TEPosition - 1].buffer
          ELSE << >> \* No previous buffer before first state of the trace

\* True if t is the executing thread in the next state.
IsScheduledThread(t) == t = Scheduled

DiffBuf(t, seq1, seq2) == 
         IF IsScheduledThread(t)
         THEN Diff(ToSet(seq1), ToSet(seq2))
         ELSE Null

\* The element that is going to be added by t in the next state or Null.
ProdBuf(t) == DiffBuf(t, nxtBuf, curBuf)

\* The element that is going to be removed from the buffer by t in the 
\* current state or Null.
ConsBuf(t) == DiffBuf(t, prvBuf, curBuf)

---------------------------------------------------------------------------
(*
 Down below it is all about the layout of the animation.  The positions
 have been created by trial and error and only work for a subset of the
 possible model parameters (e.g. location of producers, consumers, and
 buffer).  In general, this is too finicky and one would prefer something
 like Tikz's relative positioning (left-of, south-of, ...).  Maybe nested
 <svg> elements could help.
*)

Arial == [font |-> "Arial"]

---------------------------------------------------------------------------
\* Labels

Pos == [ x |-> 5, y |-> 25 ]

GWaitSet == Group(<<Text(Pos.x, Pos.y, "Wait:", Arial), 
                    Text(Pos.x + 55, Pos.y, ToString(Waiting), Arial)>>,
                  <<>>)

GRunningSet == Group(<<Text(Pos.x, Pos.y, "Run:", Arial), 
                       Text(Pos.x + 55, Pos.y, ToString(Running), Arial)>>,
                     ("transform" :> "translate(0 25)")) \* Move GRunningSet 50pts south of GWaitSet

GScheduled == Group(<<Text(Pos.x, Pos.y, "Sched:", Arial), 
                      Text(Pos.x + 60, Pos.y, ToString(Scheduled), Arial)>>,
                     ("transform" :> "translate(0 50)"))

Labels == Group(<<GWaitSet, GRunningSet, GScheduled>>, ("transform" :> "translate(20 0)"))
    
\* Buffer

BufferCellColor(i) == 
     IF ElemAt(i) = Null
     THEN "lightgray"
     ELSE "lightblue"

BPos == [w |-> 55, h |-> 55]
        
Buffer[ i \in 1..BufCapacity ] ==         
    LET label == Text(i * (BPos.w + Pos.x) + 25, Pos.y, ToString(i), Arial)
        value == Text(i * (BPos.w + Pos.x) + 25, Pos.y + 40, ToStringNull(ElemAt(i)), Arial)
        rect  == Rect(i * (BPos.w + Pos.x), Pos.y + 10, BPos.w, BPos.h, [fill |-> BufferCellColor(i)])
    IN Group(<<label, rect, value>>, <<>>)

GBuffer == Group(Buffer, ("transform" :> "translate(0 125)"))
---------------------------------------------------------------------------

CircleColor(t) == 
    IF t \in Waiting 
    THEN "red"
    ELSE IF t = Scheduled
         THEN "green"
         ELSE "yellow"

\* Producer

PPos == [ r |-> 20 ]

GProd == 
    LET seq == SetToSeq(Producers)
        F[ i \in DOMAIN seq ] == Group(<<Circle(Pos.x, i * Pos.y, PPos.r, [fill |-> CircleColor(seq[i])]),
                                         Text(Pos.x - 10,   i * Pos.y + 5, ToString(seq[i]), Arial),
                                         Text(Pos.x + 35,   i * Pos.y + 5, ToStringNull(ProdBuf(seq[i])), Arial)
                                       >>, ("transform" :> "translate(0 "\o ToString(i * 25) \o ")"))
    IN Group(F, ("transform" :> "translate(-25 70)"))

\* Consumer

GCons == 
    LET seq == SetToSeq(Consumers)
        F[ i \in DOMAIN seq ] == Group(<<Circle(Pos.x, i * Pos.y, PPos.r, [fill |-> CircleColor(seq[i])]),
                                         Text(Pos.x - 10,   i * Pos.y + 5, ToString(seq[i]), Arial),
                                         Text(Pos.x - 45,   i * Pos.y + 5, ToStringNull(ConsBuf(seq[i])), Arial)
                                       >>, ("transform" :> "translate(0 "\o ToString(i * 25) \o ")"))
    IN Group(F, ("transform" :> "translate(285 90)"))

\* Everything lumped together

Animation == SVGElemToString(Group(<<Labels, GProd, GBuffer, GCons>>, <<>>))

-----------------------------------------------------------------------------

AliascurBuf == buffer

AliasnxtBuf == buffer'

AliasWaiting == waitSet

AliasScheduled == thread

AliasConsBuf(t) == Null

AnimAlias ==
    [
        Anim |-> "<svg viewBox='-80 0 450 500'>" \o Animation \o "</svg>"
    ]

AnimInv == TLCGet("level") < 10

=============================================================================

tlc -note BlockingQueueAnim.tla -config BlockingQueue.cfg -simulate | gawk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > sprintf("%03d", n) ".svg" }'
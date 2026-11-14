----------------------- MODULE BlockingQueueJpfData ------------------------
\* Java overrides load the JPF prefix tree.  Fail closed if they are absent:
\* the replay module also requires JpfNodeCount > 0.
JpfNodeCount == 0
JpfChildren(n) == {}
JpfEvent(n) == [thread |-> "", action |-> ""]
=============================================================================

------------------------------- MODULE MCTwoClient ----------------------------- 
EXTENDS Sequences, Naturals, Integers

VARIABLES preparedMsgs, sentMsgs, rmState, tmState, tmPrepared

vars == <<preparedMsgs, sentMsgs, rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2", "rm3"} 

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


\***** INTERNAL STATES

\* A "prepared" message is waiting to be sent by the network layer.
SndPrepare(rm) == 
  /\ [type |-> "Prepared", theRM |-> rm] \notin preparedMsgs
  /\ rmState[rm] = "working"
  /\ preparedMsgs' = preparedMsgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<sentMsgs, tmState, tmPrepared>>

SndCommit(rm) ==
  /\ [type |-> "Commit"] \notin preparedMsgs
  /\ tmState \in {"init", "committed"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ preparedMsgs' = preparedMsgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<sentMsgs, tmPrepared, rmState>>

SndAbort(rm) ==
  /\ [type |-> "Abort"] \notin preparedMsgs
  /\ tmState \in {"init", "aborted"}
  /\ preparedMsgs' = preparedMsgs \cup {[type |-> "Abort"]}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<sentMsgs, tmPrepared, rmState>>

\* By contrast, message recievers depend on payload.
\* Payload delivery is controlled by client || net
RcvPrepare(rm, payload) ==
  /\ payload = [type |-> "Prepared", theRM |-> rm]
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<preparedMsgs, sentMsgs, tmState, rmState>>

RcvCommit(rm, payload) ==
  /\ payload = [type |-> "Commit"]
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<preparedMsgs, sentMsgs, tmState, tmPrepared>>

RcvAbort(rm, payload) ==
  /\ payload = [type |-> "Abort"]
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<preparedMsgs, sentMsgs, tmState, tmPrepared>>

\* At any point, we may silently abort
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<preparedMsgs, sentMsgs, tmState, tmPrepared>>


\***** NETLIB-EXPOSED API

PrepareMsg ==
    \E rm \in RMs:
        \/ SndPrepare(rm)
        \/ SndAbort(rm)
        \/ SilentAbort(rm)

\* SentMessages represent messages that have been sent over the network.
SndMsg(payload) ==
    /\ payload \notin sentMsgs
    /\ sentMsgs' = sentMsgs \cup {payload}
    /\ UNCHANGED <<preparedMsgs, rmState, tmState, tmPrepared>>

RcvMsg(payload) ==
    \E rm \in RMs:
        \/ RcvPrepare(rm, payload)
        \/ RcvCommit(rm, payload)
        \/ RcvAbort(rm, payload)


\***** SPECIFICATION

Init ==   
  /\ preparedMsgs = {}
  /\ sentMsgs = {}
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

\* In a networked system, there would be an abstraction for delivered messages.
Next == 
    \/ PrepareMsg
    \/ \E payload \in preparedMsgs: SndMsg(payload)
    \/ \E msg \in sentMsgs: RcvMsg(msg)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ preparedMsgs \in SUBSET Message
  /\ sentMsgs \in SUBSET Message
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs

\***** SAFETY PROPERTIES

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

====

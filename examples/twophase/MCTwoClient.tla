------------------------------- MODULE MCTwoClient ----------------------------- 
EXTENDS Sequences, Naturals, Integers

VARIABLES msgs, rmState, tmState, tmPrepared

vars == <<msgs, rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2", "rm3"} 

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


\***** INTERNAL STATES

\* Checking that duplicate messages are not sent so as to avoid sending redundant messages over the network lib.
\* Although in isolation it's not necessary to do this, when coupled with the added state of NetLib, it is.
SndPrepare(rm) == 
  /\ [type |-> "Prepared", theRM |-> rm] \notin msgs
  /\ rmState[rm] = "working"
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

SndCommit(rm) ==
  /\ [type |-> "Commit"] \notin msgs
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ tmState \in {"init", "committed"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

SndAbort(rm) ==
  /\ [type |-> "Abort"] \notin msgs
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>

\* By contrast, message recievers depend on payload.
\* Payload delivery is controlled by client || net
RcvPrepare(rm, payload) ==
  /\ payload = [type |-> "Prepared", theRM |-> rm]
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<msgs, tmState, rmState>>

RcvCommit(rm, payload) ==
  /\ payload = [type |-> "Commit"]
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>

RcvAbort(rm, payload) ==
  /\ payload = [type |-> "Abort"]
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>

\* At any point, we may silently abort
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


\***** NETLIB-EXPOSED API

SndMsg ==
    \E rm \in RMs:
        \/ SndPrepare(rm)
        \/ SndAbort(rm)
        \/ SilentAbort(rm)

RcvMsg(payload) ==
    \E rm \in RMs:
        \/ RcvPrepare(rm, payload)
        \/ RcvCommit(rm, payload)
        \/ RcvAbort(rm, payload)


\***** SPECIFICATION

Init ==   
  /\ msgs = {}
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

Next == 
    \/ SndMsg
    \/ \E msg \in msgs: RcvMsg(msg)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs

\***** SAFETY PROPERTIES

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

====

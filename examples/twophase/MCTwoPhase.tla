------------------------------- MODULE MCTwoPhase ----------------------------- 
EXTENDS TLC, Integers, Sequences

\* Payloads and messages are distinct: messages include additional metadata.
VARIABLES t, sentMsgs, deliveredMsgs, preparedPayloads, sentPayloads, rmState, tmState, tmPrepared

vars == <<t, sentMsgs, deliveredMsgs, preparedPayloads, sentPayloads, rmState, tmState, tmPrepared>>

clientVars == <<preparedPayloads, sentPayloads, rmState, tmState, tmPrepared>>
netVars == <<t, sentMsgs, deliveredMsgs>>

RMs == {"rm1", "rm2", "rm3"} 

Net == INSTANCE SynchLib WITH 
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs

Client == INSTANCE MCTwoClient WITH
    preparedMsgs <- preparedPayloads,
    sentMsgs <- sentPayloads,
    rmState <- rmState,
    tmState <- tmState,
    tmPrepared <- tmPrepared


\* ----- COMPOSED OPERATIONS -----

PrepareMsg == Client!PrepareMsg /\ UNCHANGED<<netVars>>

SndMsg(payload) == Client!SndMsg(payload) /\ Net!SndMsg(payload)

DeliverMsg(msg) == UNCHANGED<<clientVars>> /\ Net!DeliverMsg(msg)

RcvMsg(msg) == Client!RcvMsg(msg.payload) /\ UNCHANGED<<netVars>>

\* TODO: turn this into model checked version.
IncTime == UNCHANGED <<clientVars>> /\ t < 4 /\ Net!IncTime

TypeOK == Net!TypeOK

\* ----- Imported safety properties -----

Consistent == Client!Consistent
AllRcvedSent == Net!AllRcvedSent
AllRcvedInTime == Net!AllRcvedInTime


\* ----- SPECIFICATION

Init == Client!Init /\ Net!Init

Next ==
    \/ PrepareMsg
    \/ \E payload \in preparedPayloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ \E msg \in deliveredMsgs: RcvMsg(msg)
    \/ IncTime

Spec == Init /\ [][Next]_vars

=============================================================================

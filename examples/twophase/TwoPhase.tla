------------------------------- MODULE TwoPhase ----------------------------- 
EXTENDS TLC, Integers, Sequences

VARIABLES t, sentMsgs, deliveredMsgs, payloads, rmState, tmState, tmPrepared

vars == <<t, sentMsgs, deliveredMsgs, payloads, rmState, tmState, tmPrepared>>

clientVars == <<payloads, rmState, tmState, tmPrepared>>
netVars == <<t, sentMsgs, deliveredMsgs>>

RMs == {"rm1", "rm2", "rm3"} 

Net == INSTANCE SynchLib WITH 
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs

Client == INSTANCE TwoClient WITH
    msgs <- payloads,
    rmState <- rmState,
    tmState <- tmState,
    tmPrepared <- tmPrepared


\***** COMPOSED OPERATIONS

EnqueueMsg == Client!SndMsg /\ UNCHANGED<<netVars>>

SndMsg(payload) == UNCHANGED<<clientVars>> /\ Net!SndMsg(payload)

DeliverMsg(msg) == UNCHANGED<<clientVars>> /\ Net!DeliverMsg(msg)

DequeueMsg(msg) == Client!RcvMsg(msg.payload) /\ UNCHANGED<<netVars>>

\* TODO: turn this into model checked version.
IncTime == UNCHANGED <<clientVars>> /\ Net!IncTime

TypeOK == Net!TypeOK

\***** Imported safety properties

Consistent == Client!Consistent
AllRcvedSent == Net!AllRcvedSent
AllRcvedInTime == Net!AllRcvedInTime


\***** SPECIFICATION

Init == Client!Init /\ Net!Init

Next ==
    \/ EnqueueMsg
    \/ \E payload \in payloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ \E msg \in deliveredMsgs: DequeueMsg(msg)

Spec == Init /\ [][Next]_vars

=============================================================================

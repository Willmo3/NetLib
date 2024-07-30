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

Sys == INSTANCE Sys WITH
    msgs <- payloads,
    rmState <- rmState,
    tmState <- tmState,
    tmPrepared <- tmPrepared


\* ----- COMPOSED OPERATIONS -----

PrepareMsg == Sys!PrepareMsg /\ UNCHANGED<<netVars>>

SndMsg(payload) == UNCHANGED<<clientVars>> /\ Net!SndMsg(payload)

DeliverMsg(msg) == Sys!RcvMsg(msg.payload) /\ Net!DeliverMsg(msg)

IncTime == UNCHANGED <<clientVars>> /\ Net!IncTime


\* Fault operations

DuplicateMsg(msg) == UNCHANGED<<clientVars>> /\ Net!DuplicateMsg(msg)

\* Since message corruption is domain-specific, we have to use client code.
CorruptMsg(msg) == UNCHANGED<<clientVars>> /\ Net!CorruptMsg(msg, Sys!CorruptMsg)

DropMsg(msg) == UNCHANGED<<clientVars>> /\ Net!DropMsg(msg)



TypeOK == Net!TypeOK

\* ----- Imported safety properties -----

Consistent == Sys!Consistent
AllRcvedSent == Net!AllRcvedSent
AllRcvedInTime == Net!AllRcvedInTime


\* ----- SPECIFICATION -----

Init == Sys!Init /\ Net!Init

Next ==
    \/ PrepareMsg
    \/ \E payload \in payloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime

\* Faulty nexts

DupNext ==
    \/ Next
    \/ \E msg \in sentMsgs: DuplicateMsg(msg)

CorruptNext ==
    \/ Next
    \/ \E msg \in sentMsgs: CorruptMsg(msg)

DropNext ==
    \/ Next
    \/ \E msg \in sentMsgs: DropMsg(msg)

DropDupNext ==
    \/ DropNext
    \/ DupNext

\* Change the next to try different fault configurations!
Spec == Init /\ [][Next]_vars

=============================================================================

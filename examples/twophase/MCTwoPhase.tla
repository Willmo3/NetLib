------------------------------- MODULE MCTwoPhase ----------------------------- 
EXTENDS TLC, Integers, Sequences

\* Payloads and messages are distinct: messages include additional metadata.
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

\* To allow termination, eventually stop sending messages.
SndMsg(payload) == UNCHANGED<<clientVars>> /\ t < 6 /\ Net!SndMsg(payload)

\* For simplicity, client recieves message as soon as it's delivered.
DeliverMsg(msg) == Sys!RcvMsg(msg.payload) /\ Net!DeliverMsg(msg)

IncTime == UNCHANGED<<clientVars>> /\ t < 4 /\ Net!IncTime

\* Fault operations
\* For model checking purposes, only perform these faults up to a certain time.

DuplicateMsg(msg) == UNCHANGED<<clientVars>> /\ t < 6 /\ Net!DuplicateMsg(msg)

\* Since message corruption is domain-specific, we have to use client code.
CorruptMsg(msg) == UNCHANGED<<clientVars>> /\ t < 6 /\ Net!CorruptMsg(msg, Sys!CorruptMsg)

DropMsg(msg) == UNCHANGED<<clientVars>> /\ t < 6 /\ Net!DropMsg(msg)

TypeOK == Net!TypeOK

\* ----- Imported safety properties -----

Consistent == Sys!Consistent
AllRcvedSent == Net!AllRcvedSent
AllRcvedInTime == Net!AllRcvedInTime

\* ----- SPECIFICATION

Init == Sys!Init /\ Net!Init

\* The normative environment
Next ==
    \/ PrepareMsg
    \/ \E payload \in payloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime

\* A deviated environment 
\* where messages may be randomly duplicated.
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

\* Change the spec to evaluate against a fault configuration.
Spec == Init /\ [][Next]_vars

=============================================================================

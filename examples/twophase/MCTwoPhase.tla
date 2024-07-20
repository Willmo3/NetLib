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

Client == INSTANCE TwoClient WITH
    msgs <- payloads,
    rmState <- rmState,
    tmState <- tmState,
    tmPrepared <- tmPrepared


\* ----- COMPOSED OPERATIONS -----

PrepareMsg == Client!PrepareMsg /\ UNCHANGED<<netVars>>

\* To allow termination, eventually stop sending messages.
SndMsg(payload) == UNCHANGED<<clientVars>> /\ t < 6 /\ Net!SndMsg(payload)

\* For simplicity, client recieves message as soon as it's delivered.
DeliverMsg(msg) == Client!RcvMsg(msg.payload) /\ Net!DeliverMsg(msg)

IncTime == UNCHANGED<<clientVars>> /\ t < 4 /\ Net!IncTime

\* Fault operations

\* For model checking purposes, only duplicate messages up to a certain time.
DuplicateMsg(msg) == UNCHANGED<<clientVars>> /\ t < 4 /\ Net!DuplicateMsg(msg)

TypeOK == Net!TypeOK

\* ----- Imported safety properties -----

Consistent == Client!Consistent
AllRcvedSent == Net!AllRcvedSent
AllRcvedInTime == Net!AllRcvedInTime


\* ----- SPECIFICATION

Init == Client!Init /\ Net!Init

Next ==
    \/ PrepareMsg
    \/ \E payload \in payloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime

\* Faulty nexts

DupNext ==
    \/ Next
    \/ \E msg \in sentMsgs: DuplicateMsg(msg)

Spec == Init /\ [][Next]_vars

=============================================================================

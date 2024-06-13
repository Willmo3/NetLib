---- MODULE TestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {1, 2, 3}

\* Delta: maximum sync time bound.
VARIABLES Delta, t, sentMsgs, deliveredMsgs, rcvQueue, sentPayloads, rcvPayloads
vars == <<Delta, t, sentMsgs, deliveredMsgs, rcvQueue, sentPayloads, rcvPayloads>>

\* Variables local to network abstraction.
localVars == <<sentPayloads, rcvPayloads>>

\* Variables

Net == INSTANCE SynchLib WITH 
    Delta <- Delta,
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs,
    rcvQueue <- rcvQueue

\* Compose our ops with next ones.

SndMsg(payload) ==
    /\ ~(payload \in sentPayloads)
    /\ Net!SndMsg(payload)
    /\ sentPayloads' = sentPayloads \cup {payload}
    /\ UNCHANGED <<Delta, rcvPayloads, rcvQueue, deliveredMsgs>>

RcvMsg ==
    /\ Len(rcvQueue) > 0
    /\ rcvPayloads' = rcvPayloads \cup {Head(rcvQueue)}
    /\ rcvQueue' = Tail(rcvQueue)
    /\ UNCHANGED <<Delta, t, sentMsgs, deliveredMsgs, sentPayloads>>

DeliverMsg ==
    /\ Net!DeliverMsg
    /\ UNCHANGED <<Delta, localVars>>

IncTime ==
    /\ Net!IncTime
    /\ UNCHANGED <<Delta, localVars>>

\* Note: once all messages are sent, this will terminate.
\* Will need to add in the stuttering steps to prevent this. 

Init ==
    /\ sentPayloads = {}
    /\ rcvPayloads = {}
    /\ Delta = 16
    /\ Net!Init

Next ==
    \/ \E payload \in Payloads: SndMsg(payload)
    \/ DeliverMsg
    \/ RcvMsg
    \/ IncTime
    
Spec == Init /\ [][Next]_vars

\* Imported safety properties

AllRcvedInTime == Net!AllRcvedInTime 
AllRcvedSent == Net!AllRcvedSent
TypeOK == Net!TypeOK

====
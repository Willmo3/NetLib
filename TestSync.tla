---- MODULE TestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {1, 2, 3}

VARIABLES t, sentMsgs, deliveredMsgs, rcvQueue, sentPayloads, rcvPayloads
vars == <<t, sentMsgs, deliveredMsgs, rcvQueue, sentPayloads, rcvPayloads>>

\* Variables local to network abstraction.
localVars == <<sentPayloads, rcvPayloads>>

\* Variables

Net == INSTANCE SynchLib WITH 
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs,
    rcvQueue <- rcvQueue

\* Compose our ops with next ones.

SndMsg(payload) ==
    /\ ~(payload \in sentPayloads)
    /\ Net!SndMsg(payload)
    /\ sentPayloads' = sentPayloads \cup {payload}
    /\ UNCHANGED <<rcvPayloads, rcvQueue, deliveredMsgs>>

RcvMsg ==
    /\ Len(rcvQueue) > 0
    /\ rcvPayloads' = rcvPayloads \cup {Head(rcvQueue)}
    /\ rcvQueue' = Tail(rcvQueue)
    /\ UNCHANGED <<t, sentMsgs, deliveredMsgs, sentPayloads>>

DeliverMsg ==
    /\ Net!DeliverMsg
    /\ UNCHANGED <<localVars>>

\* Note: once all messages are sent, this will terminate.
\* Will need to add in the stuttering steps to prevent this. 

Init ==
    /\ sentPayloads = {}
    /\ rcvPayloads = {}
    /\ Net!Init

Next ==
    \/ \E payload \in Payloads: SndMsg(payload)
    \/ DeliverMsg
    \/ RcvMsg
    
Spec == Init /\ [][Next]_vars

\* Goal: eventually, every payload that we sent will be recieved.
\* AllRecieved == <>(rcvedPayloads = Payloads)

====
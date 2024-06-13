---- MODULE MCTestSync ----
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

IncTime ==
    /\ Net!IncTime
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
    \/ (t < Net!Delta /\ IncTime)
    
Spec == Init /\ [][Next]_vars

\* Goal: eventually, every payload that we sent will be recieved.
\* AllRecieved == <>(rcvedPayloads = Payloads)

\* ----- SAFETY PROPERTIES -----

\* Synchronous network communication includes an upper bound on message delivery time.
\* Hence, it can be represented by the following two safety properties:

\* For all sent messages,
\* If at any point, that message is not in the set of recieved messages
\* And more than \delta time has passed since it was recieved
\* Then a safety property is violated!
AllRcvedInTime == \A msg \in sentMsgs : (msg \in deliveredMsgs \/ t <= msg.time + Net!Delta)

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!
AllRcvedSent == \A msg \in deliveredMsgs : msg \in sentMsgs

====
---- MODULE MCTestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {1, 2, 3}

\* Delta: maximum time between.
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
    \/ (t < Delta /\ IncTime)
    
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
AllRcvedInTime == \A msg \in sentMsgs : (msg \in deliveredMsgs \/ t <= msg.time + Delta)

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!
AllRcvedSent == \A msg \in deliveredMsgs : msg \in sentMsgs

====
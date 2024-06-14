---- MODULE MCTestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {"a", "b", "c"}

\* TODO: eventually cond?

\* Delta: maximum sync time bound.
VARIABLES Delta, t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads
vars == <<Delta, t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads>>

\* TODO: don't reference shared variables

\* Variables local to network abstraction.
localVars == <<sentPayloads, rcvPayloads>>

\* Change Delta to constant.
Net == INSTANCE SynchLib WITH 
    Delta <- Delta,
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs

\* COMPOSED OPERATIONS
SndMsg(payload) ==
    /\ payload \notin sentPayloads
    /\ Net!SndMsg(payload)
    /\ sentPayloads' = sentPayloads \cup {payload}
    /\ UNCHANGED <<Delta, rcvPayloads, deliveredMsgs>>

DeliverMsg(msg) ==
    /\ Net!DeliverMsg(msg)
    /\ rcvPayloads' = rcvPayloads \cup {msg.payload}
    /\ UNCHANGED <<Delta, sentPayloads>>

IncTime ==
    /\ t < Delta
    /\ Net!IncTime
    /\ UNCHANGED <<Delta, localVars>>

\* SPECIFICATION
Init ==
    /\ sentPayloads = {}
    /\ rcvPayloads = {}
    /\ Delta = 16
    /\ Net!Init

Next ==
    \/ \E payload \in Payloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime
    
Spec == Init /\ [][Next]_vars

\* Imported safety properties

AllRcvedInTime == Net!AllRcvedInTime 
AllRcvedSent == Net!AllRcvedSent
TypeOK == Net!TypeOK

====
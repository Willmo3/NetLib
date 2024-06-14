---- MODULE TestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {"a", "b", "c"}

\* Delta: maximum sync time bound.
VARIABLES t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads
vars == <<t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads>>

\* TODO: don't reference shared variables

\* Variables local to network abstraction.
clientVars == <<sentPayloads, rcvPayloads>>

\* Change Delta to constant.
Net == INSTANCE SynchLib WITH 
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs

Client == INSTANCE SynchClient WITH 
    sentPayloads <- sentPayloads,
    rcvPayloads <- rcvPayloads

\* COMPOSED OPERATIONS
SndMsg(payload) == Net!SndMsg(payload) /\ Client!SndMsg(payload)

DeliverMsg(msg) == Net!DeliverMsg(msg) /\ Client!DeliverMsg(msg)

IncTime == Net!IncTime /\ UNCHANGED <<clientVars>>

\* SPECIFICATION
Init == Net!Init /\ Client!Init

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
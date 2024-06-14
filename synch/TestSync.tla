---- MODULE TestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {"a", "b", "c"}

VARIABLES t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads
vars == <<t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads>>
clientVars == <<sentPayloads, rcvPayloads>>

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

\* Imported safety properties

AllRcvedInTime == Net!AllRcvedInTime 
AllRcvedSent == Net!AllRcvedSent
TypeOK == Net!TypeOK
AllEventuallyRcved == Client!AllEventuallyRcved

\* SPECIFICATION
Init == Net!Init /\ Client!Init

Next ==
    \/ \E payload \in Payloads: SndMsg(payload)
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime

Spec == Init /\ [][Next]_vars

\* We delegate a lot to the network
FairSpec == Spec /\ WF_vars(Next)

====
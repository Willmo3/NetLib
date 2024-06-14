---- MODULE MCTestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.
\* Parallel composition of this testing with SynchLib.

Payloads == {"a", "b", "c"}

VARIABLES t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads
vars == <<t, sentMsgs, deliveredMsgs, sentPayloads, rcvPayloads>>
clientVars == <<sentPayloads, rcvPayloads>>
netVars == <<t, sentMsgs, deliveredMsgs>>

Net == INSTANCE SynchLib WITH 
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs

Client == INSTANCE NetClient WITH 
    sentPayloads <- sentPayloads,
    rcvPayloads <- rcvPayloads

\* COMPOSED OPERATIONS
SndMsg(payload) == Client!SndMsg(payload) /\ Net!SndMsg(payload)

DeliverMsg(msg) == UNCHANGED <<clientVars>> /\ Net!DeliverMsg(msg)

RcvMsg(payload) == Client!RcvMsg(payload) /\ UNCHANGED <<netVars>>

\* Checking that t < delta to limit state space and prevent a ton of extra time steps.
IncTime == UNCHANGED <<clientVars>> /\ t < Net!Delta /\ Net!IncTime

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
    \/ \E msg \in deliveredMsgs: RcvMsg(msg.payload)
    \/ IncTime
    
Spec == Init /\ [][Next]_vars
\* In order to guarantee message arrival, need to allow fairness.
\* Given that this is a synchronous network, some guarantee of fairness is natural anyways.
FairSpec == Spec /\ WF_vars(Next)

====
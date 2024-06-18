---- MODULE PartialLib ----
EXTENDS TLC, Integers

\* The upper bound on logical communication time.
\* This does not apply to asynchronous networks.
Delta == 8

\* Network Global Stabilization Time
\* Applies only for partially synchronous networks
GST == 16


\* ----- VARIABLES -----

\* t: current logical time
\* sentMsgs: set of all messages explicitly sent by our system
\* deliveredMsgs: set of all messages delivered by our system
VARIABLES t, sentMsgs, deliveredMsgs

vars == <<t, sentMsgs, deliveredMsgs>>


\* ----- IMPORTS -----

Channel == INSTANCE NetLib WITH
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs


\* ----- HELPER PREDICATES -----

\* Assuming we've reached GST:
\* Is there a message which:
\* -- Was sent after GST
\* -- Needs to be sent now or will expire delta!
UrgentMsg == 
    /\ t >= GST
    /\ \E msg \in sentMsgs : 
        /\ msg \notin deliveredMsgs
        /\ msg.time >= GST
        /\ msg.time + Delta = t


\* ----- SAFETY PROPERTIES -----

\* No message should be recieved if it was not first sent.
AllRcvedSent == Channel!AllRcvedSent

\* A variant of all recieved in time.
\* If a message was sent after the GST, then it should respect delta.
AllRcvedInTimeAfterGST == \A msg \in sentMsgs:
    \/ msg.time < GST 
    \/ msg \in deliveredMsgs 
    \/ t <= msg.time + Delta

    TypeOK == Channel!TypeOK


\* ----- STATES -----

SndMsg(payload) ==
    /\ ~UrgentMsg
    /\ Channel!SndMsg(payload)

DeliverMsg(msg) ==
    /\ UrgentMsg => msg.time + Delta = t
    /\ Channel!DeliverMsg(msg)

IncTime ==
    /\ ~UrgentMsg
    /\ Channel!IncTime


\* ----- MODEL RUNNERS -----

Init == Channel!Init

\* This next will continue endlessly delivering empty messages.
\* NetLib is meant to be composed with another library.
Next == 
    \/ SndMsg("")
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime

Spec == Init /\ [][Next]_vars

====
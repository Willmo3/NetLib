---- MODULE PartialLib ----
EXTENDS TLC, Integers

\* The upper bound on logical communication time.
\* In a partially synchronous network, this delta is hidden -- i.e. unknown
\* This is equivalent to the GST definition of asynchronous networks.
HiddenDelta == 16


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

\* Is there a message which:
\* -- Hasn't yet been delivered
\* -- Needs to be sent now or will expire the hidden delta!
UrgentMsg == \E msg \in sentMsgs : 
    /\ msg \notin deliveredMsgs
    /\ msg.time + HiddenDelta = t


\* ----- SAFETY PROPERTIES -----

\* No message should be recieved if it was not first sent.
AllRcvedSent == Channel!AllRcvedSent

\* Since the hidden delta includes the GST in it
\* Simply changing AllRcvedInTime to use HiddenDelta indicates it's recieved after GST
AllRcvedInTimeAfterGST == \A msg \in sentMsgs:
    \/ msg \in deliveredMsgs 
    \/ t <= msg.time + HiddenDelta

TypeOK == Channel!TypeOK


\* ----- STATES -----

SndMsg(payload) ==
    /\ ~UrgentMsg
    /\ Channel!SndMsg(payload)

DeliverMsg(msg) ==
    /\ UrgentMsg => msg.time + HiddenDelta = t
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
---- MODULE SynchLib ----
EXTENDS TLC, Integers

\* ----- CONSTANTS -----

\* The upper bound on logical communication time.
Delta == 8


\* ----- VARIABLES -----

\* t: current logical time
\* sentMsgs: set of all messages explicitly sent by our system
\* deliveredMsgs: set of all messages delivered by our system
VARIABLES t, sentMsgs, deliveredMsgs

vars == <<t, sentMsgs, deliveredMsgs>>


\* ----- IMPORTS -----

Channel == INSTANCE NetChannel WITH
    t <- t,
    sentMsgs <- sentMsgs,
    deliveredMsgs <- deliveredMsgs


\* ----- HELPER PREDICATES -----

\* Is there a message which:
\* -- Is about to expire its max delivery time
\* -- Hasn't yet been delivered
UrgentMsg == \E msg \in sentMsgs : (msg.time + Delta = t /\ msg \notin deliveredMsgs)


\* ----- SAFETY PROPERTIES -----

AllRcvedSent == Channel!AllRcvedSent

\* In a synchronous library, AllEventuallyDelivered is an unnecessarily weak guarantee.
\* Instead, all messages must be recieved by delta time.
AllRcvedInTime == \A msg \in sentMsgs : (msg \in deliveredMsgs \/ t <= msg.time + Delta)

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

\* ----- FAULTS -----
\* Some of these faults change the character of a synchronous network -- for instance, messages being dropped.

DropMsg(msg) == Channel!DropMsg(msg)

DuplicateMsg(msg) == 
    /\ ~UrgentMsg
    /\ Channel!DuplicateMsg(msg)

CorruptMsg(msg, payload) == Channel!CorruptMsg(msg, payload)


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

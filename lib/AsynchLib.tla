---- MODULE AsynchLib ----
EXTENDS TLC, Integers


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


\* ----- SAFETY PROPERTIES -----

\* No message should be recieved if it was not first sent.
AllRcvedSent == Channel!AllRcvedSent

\* TODO: add all eventually recieved


\* ----- STATES -----
SndMsg(payload) == Channel!SndMsg(payload)

DeliverMsg(msg) == Channel!DeliverMsg(msg)

IncTime == Channel!IncTime


\* ----- MODEL RUNNERS -----

Init == Channel!Init

\* This next will continue endlessly delivering empty messages.
\* NetLib is meant to be composed with another library.
Next == Channel!Next

Spec == Init /\ [][Next]_vars


====
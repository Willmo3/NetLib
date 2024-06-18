---- MODULE NetLib ----
EXTENDS TLC, Integers

\* ----- VARIABLES -----

\* t: current logical time
\* sentMsgs: set of all messages explicitly sent by our system
\* deliveredMsgs: set of all messages delivered by our system
VARIABLES t, sentMsgs, deliveredMsgs

vars == <<t, sentMsgs, deliveredMsgs>>


\* ----- TYPE PROPERTY -----

\* Delta must be at least one.
\* All messages must have a time.
\* The time must be greater than or equal to 0

Message == [time : Nat, payload: STRING]

TypeOK ==
    /\ t \in Nat
    /\ \A msg \in sentMsgs : msg \in Message
    /\ \A msg \in deliveredMsgs : msg \in Message


\* ----- STATES -----

\* Note: because each message must be unique due to the changing logical time,
\* We do not need to check whether it's already in the set
SndMsg(payload) ==
    /\ sentMsgs' = sentMsgs \cup {[time |-> t, payload |-> payload]}
    /\ t' = t + 1
    /\ UNCHANGED<<deliveredMsgs>>

\* A message that has been sent but not delivered may be delivered at any point.
\* Only deliver a message if there isn't another one that needs to be delivered right now!
\* (Or if this is the message that needs to be delivered right now!)
DeliverMsg(msg) ==
    /\ msg \notin deliveredMsgs
    /\ deliveredMsgs' = deliveredMsgs \cup {msg}
    /\ t' = t + 1
    /\ UNCHANGED<<sentMsgs>>

\* To represent network delays, the network time can be incremented randomly at any point.
IncTime ==
    /\ t' = t + 1
    /\ UNCHANGED<<sentMsgs, deliveredMsgs>>


\* ----- SAFETY PROPERTIES -----

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!
AllRcvedSent == \A msg \in deliveredMsgs : msg \in sentMsgs

\* Assume this is a reliable channel: i.e. messages cannot be lost.
AllEventuallyRecieved == <>(\A msg \in sentMsgs : msg \in deliveredMsgs)


\* ----- MODEL RUNNERS -----

Init == 
    /\ t = 0
    /\ sentMsgs = {}
    /\ deliveredMsgs = {}

\* This next will continue endlessly delivering empty messages.
\* NetLib is meant to be composed with another library.
Next ==
    \/ SndMsg("")
    \/ \E msg \in sentMsgs: DeliverMsg(msg)
    \/ IncTime

====

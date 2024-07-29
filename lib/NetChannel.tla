---- MODULE NetChannel ----
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

\* Message == [time : Nat, payload: STRING]

TypeOK ==
    /\ t \in Nat
    /\ \A msg \in sentMsgs : msg.time \in Nat
    /\ \A msg \in deliveredMsgs : msg.time \in Nat


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


\* ----- FAULTS -----
\* Used for deviation models in robustness.

\* Duplicate a message that has already been sent
\* Note that this message may have been delivered!
DuplicateMsg(msg) ==
    /\ msg \in sentMsgs
    /\ sentMsgs' = sentMsgs \cup {[time |-> t, payload |-> msg.payload]}
    /\ t' = t + 1
    /\ UNCHANGED <<deliveredMsgs>>

\* Drop a message that has not yet been delivered. 
DropMsg(msg) ==
    /\ msg \notin deliveredMsgs
    /\ sentMsgs' = sentMsgs \ {msg} 
    /\ UNCHANGED <<t, deliveredMsgs>>

\* A corrupted message takes an already sent message and gives it a new payload. 
CorruptMsg(msg, newpayload) ==
    /\ msg \in sentMsgs
    /\ msg \notin deliveredMsgs
    /\ sentMsgs' = (sentMsgs \ {msg}) \cup {[time |-> msg.time, payload |-> newpayload]}
    /\ UNCHANGED <<t, deliveredMsgs>>


\* ----- SAFETY PROPERTIES -----

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!
AllRcvedSent == deliveredMsgs \in SUBSET sentMsgs

\* In our channel, every message is guaranteed to be recieved at some point.
AllEventuallyDelivered == <>[](\A msg \in sentMsgs : msg \in deliveredMsgs)

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

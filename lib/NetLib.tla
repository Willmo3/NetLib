---- MODULE NetLib ----
EXTENDS TLC, Integers, Sequences


\* Partially synchronous -- what to do?
\* Define some GST and some DELTA
\* Partially Asynchronous safe. safe: For all messages M, if m.time > GST, then t < m.time + DELTA

\* CONSTANTS


\* What type of network is this?
\* OPTIONS: "sync", "async", "partial"
NetType == "sync"

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

\* ----- SAFETY PROPERTIES -----

\* Synchronous network communication includes an upper bound on message delivery time.
\* Hence, it can be represented by the following safety property:

\* For all sent messages,
\* Either it must have already been delivered
\* Or less than \delta time has passed since it was recieved

\* By definition, this property does not hold for asynchronous networks.
AllRcvedInTime == \A msg \in sentMsgs : (msg \in deliveredMsgs \/ t <= msg.time + Delta)

\* A variant of all recieved in time.
\* If a message was sent after the GST, then it should respect delta.
AllRcvedInTimeAfterGST == \A msg \in sentMsgs : (
    \/ msg.time < GST 
    \/ msg \in deliveredMsgs 
    \/ t <= msg.time + Delta)

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!
AllRcvedSent == \A msg \in deliveredMsgs : msg \in sentMsgs


\* ----- TYPE PROPERTY -----

\* Delta must be at least one.
\* All messages must have a time.
\* The time must be greater than or equal to 0

Message == [time : Nat, payload: STRING]

TypeOK ==
    /\ NetType \in {"sync", "async", "partial"}
    /\ t \in Nat
    /\ \A msg \in sentMsgs : msg \in Message
    /\ \A msg \in deliveredMsgs : msg \in Message


\* ----- HELPER PREDICATES -----

\* Is there a message that urgently needs to be delivered?
\* First off: is our network currently synchronous (GST passed or always sync?)
\* If not, no guarantees about message urgency
\* This is true if there's a message which:
\* -- Is about to expire its max delivery time
\* -- Hasn't yet been delivered

UrgentMsg == 
    /\ (NetType = "sync" \/ (NetType = "partial" /\ t >= GST))
    /\ \E msg \in sentMsgs : (msg.time + Delta = t /\ msg \notin deliveredMsgs)


\* ----- STATES -----

\* Only send a message if there isn't one that needs to be delivered right now!

\* Note: because each message must be unique due to the changing logical time,
\* We do not need to check whether it's already in the set
SndMsg(payload) ==
    /\ ~UrgentMsg
    /\ sentMsgs' = sentMsgs \cup {[time |-> t, payload |-> payload]}
    /\ t' = t + 1
    /\ UNCHANGED<<deliveredMsgs>>

\* A message that has been sent but not delivered may be delivered at any point.
\* Only deliver a message if there isn't another one that needs to be delivered right now!
\* (Or if this is the message that needs to be delivered right now!)
DeliverMsg(msg) ==
    /\ UrgentMsg => msg.time + Delta = t
    /\ msg \notin deliveredMsgs
    /\ deliveredMsgs' = deliveredMsgs \cup {msg}
    /\ t' = t + 1
    /\ UNCHANGED<<sentMsgs>>

\* To represent network delays, the network time can be incremented randomly at any point.
IncTime ==
    /\ ~UrgentMsg
    /\ t' = t + 1
    /\ UNCHANGED<<sentMsgs, deliveredMsgs>>


\* ----- MODEL RUNNERS -----

Init == 
    /\ t = 0
    /\ sentMsgs = {}
    /\ deliveredMsgs = {}

\* TODO: By convention, include next

====
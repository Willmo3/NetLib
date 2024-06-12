---- MODULE SynchLib ----
EXTENDS TLC, Integers, Sequences


\* ----- CONSTANTS -----

\* Not defined in model cfg file to support recomp-verify

\* The upper bound on time between message delivery.
\* Must be at least two -- i.e. one time step to send message and one time step to deliver
Delta == 32


\* ----- VARIABLES -----

\* t: current logical time
\* sentMsgs: set of all messages explicitly sent by our system
\* deliveredMsgs: set of all messages delivered by our system
\* rcvQueue: queue of messages to be recieved.
VARIABLES t, sentMsgs, deliveredMsgs, rcvQueue

vars == <<t, sentMsgs, deliveredMsgs, rcvQueue>>

\* ----- SAFETY PROPERTIES -----

\* Synchronous network communication includes an upper bound on message delivery time.
\* Hence, it can be represented by the following two safety properties:

\* For all sent messages,
\* If at any point, that message is not in the set of recieved messages
\* And more than \delta time has passed since it was recieved
\* Then a safety property is violated!
AllRcvedInTime == \A msg \in sentMsgs : (msg \in deliveredMsgs \/ t <= msg.time + Delta)

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!
AllRcvedSent == \A msg \in deliveredMsgs : msg \in sentMsgs


\* ----- TYPE PROPERTY -----

\* All messages must have a time.
\* The time must be greater than or equal to 0
\* TODO: can we check that payload exists?

TypeOK ==
    /\ t >= 0
    /\ \A msg \in sentMsgs : (msg.time >= 0)
    /\ \A msg \in deliveredMsgs : (msg.time >= 0)
    /\ rcvQueue \in SUBSET deliveredMsgs

\* ----- HELPER PREDICATES -----

\* Is there a message that urgently needs to be delivered?
\* This is true if there's a message which:
\* -- Is about to expire its max delivery time
\* -- Hasn't yet been delivered
UrgentMsg == \E msg \in sentMsgs : (msg.time + Delta = t /\ ~(msg \in deliveredMsgs))


\* ----- STATES -----

\* Only send a message if there isn't one that needs to be delivered right now!

\* Note: because each message must be unique due to the changing logical time,
\* We do not need to check whether it's already in the set
SndMsg(payload) ==
    /\ ~UrgentMsg
    /\ sentMsgs' = sentMsgs \cup {[time |-> t, payload |-> payload]}
    /\ t' = t + 1
    /\ UNCHANGED<<deliveredMsgs, rcvQueue>>

\* A message that has been sent but not delivered may be delivered at any point.
\* Only deliver a message if there isn't another one that needs to be delivered right now!
\* (Or if this is the message that needs to be delivered right now!)
DeliverMsg(msg) ==
    /\ msg \in sentMsgs
    /\ ~(msg \in deliveredMsgs)
    /\ (msg.time + Delta = t \/ ~UrgentMsg)
    /\ deliveredMsgs' = deliveredMsgs \cup {msg}
    /\ rcvQueue' = Append(rcvQueue, msg)
    /\ t' = t + 1
    /\ UNCHANGED<<sentMsgs>>


\* ----- MODEL RUNNERS -----

\* NOTE: change msgs to change what's inside!
Init == 
    /\ t = 0
    /\ sentMsgs = {}
    /\ deliveredMsgs = {}
    /\ rcvQueue = <<>>

====
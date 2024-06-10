---- MODULE SynchLib ----
EXTENDS TLC, Integers

\* CONSTANTS
\* Not defined in model cfg file to support recomp-verify

\* The upper bound on time between message delivery.
Delta == 32

\* VARIABLES

\* t: current logical time
\* sentMsgs: set of all messages explicitly sent by our system
\* rcvedMsgs: set of all messages recieved by our system
\* rcvQueue: queue of messages to be removed.
VARIABLES t, sentMsgs, rcvedMsgs, rcvQueue

vars == <<t, sentMsgs, rcvedMsgs, rcvQueue>>

\* SAFETY PROPERTIES
\* Synchronous network communication includes an upper bound on message delivery time.
\* Hence, it can be represented by the following two safety properties:

\* For all sent messages,
\* If at any point, that message is not in the set of recieved messages
\* And more than \delta time has passed since it was recieved
\* Then a safety property is violated!

AllRcvedInTime == \A msg \in sentMsgs : (msg \in rcvedMsgs \/ t <= msg.time + Delta)

\* For all recieved messages,
\* If that message was never sent
\* Then a safety property is violated!

AllRcvedSent == \A msg \in rcvedMsgs : msg \in sentMsgs





\* A message contains at least a timestep plus some user-defined payload.
\* Message == [time: {0..N}, ...]

====
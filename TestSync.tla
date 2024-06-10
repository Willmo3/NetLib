---- MODULE TestSync ----
EXTENDS TLC, Integers, Sequences

\* This tests the sychronous lib with a litany of messages.

Net == INSTANCE SynchLib WITH 
    t <- 0, 
    sentMsgs <- {},
    deliveredMsgs <- {},
    rcvQueue <- <<>>,
    latestMsg <- {}

\* Send three messages, then dequeue them once recieved.
\* Goal: recieved messages should eventually be identical to messages

Payloads == {1, 2, 3}

VARIABLES sntPayloads, rcvedPayloads
vars == <<sntPayloads, rcvedPayloads>>

\* Recieve the payload of the latest message recieved.
\* TODO: eventually, maybe put this in synch lib?
RcvPayload ==
    /\ Len(Net!RcvQueue) > 0
    /\ Net!RcvMsg
    /\ rcvedPayloads = rcvedPayloads \cup {Net!LatestMsg.payload}

\* Goal: eventually, every payload that we sent will be recieved.
\* AllRecieved == <>(rcvedPayloads = Payloads)

Init ==
    /\ sntPayloads = {}
    /\ rcvedPayloads = {}

\* Note: once all messages are sent, this will terminate.
\* Will need to add in the stuttering steps to prevent this. 
Next ==
    \/ (\E payload \in Payloads:
        /\ ~(payload \in sntPayloads)
        /\ Net!SndMsg(payload))
    \/ RcvPayload

Spec == (Init /\ Net!Init) /\ [][Next \/ Net!Next]_vars
THEOREM Spec => Net!Spec

====
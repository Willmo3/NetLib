---- MODULE NetClient ----
EXTENDS TLC

\* A simple client interfacing with our network library.

\* Clients interface with "payloads" -- network messages stripped of their metadata.
Payloads == {"a", "b", "c"}

VARIABLES sentPayloads, rcvPayloads
vars == <<sentPayloads, rcvPayloads>>

\* A client may send a payload or recieve a payload.
SndMsg(payload) ==
    /\ payload \notin sentPayloads
    /\ sentPayloads' = sentPayloads \cup {payload}
    /\ UNCHANGED <<rcvPayloads>>

RcvMsg(payload) ==
    /\ payload \notin rcvPayloads
    /\ rcvPayloads' = rcvPayloads \cup {payload}
    /\ UNCHANGED <<sentPayloads>>

Init ==
    /\ sentPayloads = {}
    /\ rcvPayloads = {}

\* Common goal: eventually, all payloads are recieved.
AllEventuallyRcved == <>(rcvPayloads = Payloads)

====
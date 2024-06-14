---- MODULE SynchClient ----
EXTENDS TLC

\* TODO: eventually cond?
Payloads == {"a", "b", "c"}

VARIABLES sentPayloads, rcvPayloads
vars == <<sentPayloads, rcvPayloads>>

SndMsg(payload) ==
    /\ payload \notin sentPayloads
    /\ sentPayloads' = sentPayloads \cup {payload}
    /\ UNCHANGED <<rcvPayloads>>

DeliverMsg(msg) ==
    /\ rcvPayloads' = rcvPayloads \cup {msg.payload}
    /\ UNCHANGED <<sentPayloads>>

Init ==
    /\ sentPayloads = {}
    /\ rcvPayloads = {}

AllEventuallyRcved == <>(rcvPayloads = Payloads)

====
---- MODULE SynchLib ----
EXTENDS TLC

\* The upper bound on time between message delivery.
Delta == 32

\* The current logical time.
T == 0

\* A message contains at least a timestep plus some user-defined payload.
\* Message == [time: {0..N}, ...]

====
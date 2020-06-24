FSM Readme
==========

This package defines data structures for representing finite
state machines and includes a useful theorem that asserts that
if each transition preserves some invariant, and the invariant is
satisfied by the initial state of the machine, then every input/state
combination reachable by the machine satisfies the invariant.

In addition, I include a simple finite state machine that accepts
an arbitrary binary string and outputs 1 iff the number represented
by the string is divisible by 3.

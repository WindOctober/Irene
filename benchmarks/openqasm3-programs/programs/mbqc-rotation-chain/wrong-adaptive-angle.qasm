OPENQASM 3.0;
include "stdgates.inc";

qubit[3] q;
bit first_outcome;
bit second_outcome;

reset q[1];
reset q[2];
h q[1];
h q[2];
cz q[0], q[1];
cz q[1], q[2];

rz(pi / 4) q[0];
h q[0];
first_outcome = measure q[0];

// The second measurement basis ignores the first outcome.
rz(pi / 8) q[1];
h q[1];
second_outcome = measure q[1];

if (first_outcome == true) z q[2];
if (second_outcome == true) x q[2];

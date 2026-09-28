OPENQASM 3.0;
include "stdgates.inc";

qubit data;
qubit magic;
bit outcome;

reset magic;
ry(pi / 4) magic;
cy magic, data;
s magic;
h magic;
outcome = measure magic;

// The correction is attached to the opposite measurement outcome.
if (outcome == true) ry(pi / 2) data;

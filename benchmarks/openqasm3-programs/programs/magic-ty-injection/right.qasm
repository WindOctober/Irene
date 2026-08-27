OPENQASM 3.0;
include "stdgates.inc";

qubit data;
qubit magic;
bit outcome;

reset magic;
ry(pi / 4) magic;
cy magic, data;

// Measure the consumed magic state in the Y basis.
s magic;
h magic;
outcome = measure magic;
if (outcome == false) ry(pi / 2) data;

OPENQASM 3.0;
include "stdgates.inc";

qubit[3] q;

reset q[1];
reset q[2];
rz(pi / 4) q[0];
h q[0];
rz(pi / 8) q[0];
h q[0];

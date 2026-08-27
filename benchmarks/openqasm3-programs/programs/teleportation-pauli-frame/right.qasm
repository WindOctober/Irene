OPENQASM 3.0;
include "stdgates.inc";

qubit[3] q;
bit m0;
bit m1;
bit raw;
bit result;

reset q[1];
reset q[2];
h q[1];
cx q[1], q[2];
cx q[0], q[1];
h q[0];
m0 = measure q[0];
m1 = measure q[1];
raw = measure q[2];
result = raw ^ m1;

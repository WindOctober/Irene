OPENQASM 3.0;
include "stdgates.inc";

qubit[4] q;
bit forward_bit;
bit backward_bit;

reset q[1];
reset q[2];
h q[1];
cx q[1], q[2];

cx q[0], q[1];
forward_bit = measure q[1];
if (forward_bit == true) {
  x q[2];
}

cx q[2], q[3];
h q[2];
backward_bit = measure q[2];

// The phase feed-forward from the remote target is lost.

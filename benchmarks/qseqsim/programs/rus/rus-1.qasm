OPENQASM 3.0;
include "stdgates.inc";
bit[1] c;
qubit[2] q;
h q[0];
t q[0];
cx q[0], q[1];
h q[0];
cx q[0], q[1];
t q[0];
h q[0];
c[0] = measure q[0];
while (c == 1) {
  x q[0];
  h q[0];
  t q[0];
  cx q[0], q[1];
  h q[0];
  cx q[0], q[1];
  t q[0];
  h q[0];
  c[0] = measure q[0];
}

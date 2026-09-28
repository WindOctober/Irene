OPENQASM 3.0;
include "stdgates.inc";

const int[32] n = 10;
const float[32] theta = 3 * pi / 8;

qubit q;
qubit[1] r;
angle[n] c;

reset q;
reset r[0];
h r[0];

uint[n] power = 1;
for uint i in [0:n - 1] {
  reset q;
  h q;
  ctrl @ pow(power) @ phase(theta) q, r[0];
  U(pi / 2, 0, pi - c) q;
  measure q -> c[0];
  c <<= 1;
  power <<= 1;
}

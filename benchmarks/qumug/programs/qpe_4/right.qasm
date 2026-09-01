// QUMUG GA first-order mutant: rx_gate at gate position 8, parameters [-0.08975436064453944, 0.09330057151671961, 0.32305716595672607]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[3];
qreg psi[1];
h q[0];
h q[1];
h q[2];
x psi[0];
cp(pi) psi[0],q[0];
swap q[0],q[2];
h q[0];
cp(-pi/2) q[1],q[0];
rx(-0.08975436064453944) q[1];
h q[1];
cp(-pi/4) q[2],q[0];
cp(-pi/2) q[2],q[1];
h q[2];
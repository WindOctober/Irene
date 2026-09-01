// QUMUG GA first-order mutant: rx_gate at gate position 1, parameters [-0.05969487942501369, 0.44582620292210084, 0.5]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[2];
qreg psi[1];
h q[0];
rx(-0.05969487942501369) q[1];
h q[1];
x psi[0];
cp(pi) psi[0],q[0];
swap q[0],q[1];
h q[0];
cp(-pi/2) q[1],q[0];
h q[1];
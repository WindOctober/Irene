// QUMUG GA first-order mutant: rx_gate at gate position 0, parameters [-0.021977319421610672, 0.40742385634455547, 0.04521527339527311]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[4];
rx(-0.021977319421610672) q[3];
h q[3];
cp(pi/2) q[3],q[2];
h q[2];
cp(pi/4) q[3],q[1];
cp(pi/2) q[2],q[1];
h q[1];
cp(pi/8) q[3],q[0];
cp(pi/4) q[2],q[0];
cp(pi/2) q[1],q[0];
h q[0];
swap q[0],q[3];
swap q[1],q[2];
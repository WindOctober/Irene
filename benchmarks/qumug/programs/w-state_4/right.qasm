// QUMUG GA first-order mutant: rx_gate at gate position 11, parameters [-0.008167516725914661, 0.3585589313536562, 0.3058815793210373]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[4];
ry(-pi/4) q[0];
ry(-0.9553166181245093) q[1];
ry(-pi/3) q[2];
x q[3];
cz q[3],q[2];
ry(pi/3) q[2];
cz q[2],q[1];
ry(0.9553166181245093) q[1];
cz q[1],q[0];
ry(pi/4) q[0];
cx q[2],q[3];
rx(-0.008167516725914661) q[2];
cx q[1],q[2];
cx q[0],q[1];
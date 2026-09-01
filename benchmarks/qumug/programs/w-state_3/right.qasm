// QUMUG GA first-order mutant: rz_gate at gate position 0, parameters [0.09716023324498901, 0.4873004286531119, 0.2720331864973366]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[3];
rz(0.09716023324498901) q[0];
ry(-pi/4) q[0];
ry(-0.9553166181245093) q[1];
x q[2];
cz q[2],q[1];
ry(0.9553166181245093) q[1];
cz q[1],q[0];
ry(pi/4) q[0];
cx q[1],q[2];
cx q[0],q[1];
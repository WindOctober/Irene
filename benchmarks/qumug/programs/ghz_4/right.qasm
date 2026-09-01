// QUMUG GA first-order mutant: rz_gate at gate position 3, parameters [-0.011511459338763297, 0.4591973027867907, 0.5]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[4];
h q[3];
cx q[3],q[2];
cx q[2],q[1];
rz(-0.011511459338763297) q[0];
cx q[1],q[0];
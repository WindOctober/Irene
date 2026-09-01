// QUMUG GA first-order mutant: rx_gate at gate position 4, parameters [-0.014459156081319091, 0.5, 0.25458070382378206]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[5];
h q[4];
cx q[4],q[3];
cx q[3],q[2];
cx q[2],q[1];
rx(-0.014459156081319091) q[0];
cx q[1],q[0];
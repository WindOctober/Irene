// QUMUG GA first-order mutant: rx_gate at gate position 5, parameters [-0.0032229549461747723, 5.971222855796062, 0.4297058408487564]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[6];
h q[5];
cx q[5],q[4];
cx q[4],q[3];
cx q[3],q[2];
cx q[2],q[1];
rx(-0.0032229549461747723) q[0];
cx q[1],q[0];
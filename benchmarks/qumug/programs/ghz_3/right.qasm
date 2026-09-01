// QUMUG GA first-order mutant: ry_gate at gate position 2, parameters [0.052512254801686996, 0.029517036487844997, 0.42643281039091185]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[3];
h q[2];
cx q[2],q[1];
ry(0.052512254801686996) q[0];
cx q[1],q[0];
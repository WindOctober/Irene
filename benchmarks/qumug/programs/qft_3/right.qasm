// QUMUG GA first-order mutant: rz_gate at gate position 6, parameters [0.05983559455713557, 0.4971762303363736, 0.2366494660884294]
OPENQASM 2.0;
include "qelib1.inc";
qreg q[3];
h q[2];
cp(pi/2) q[2],q[1];
h q[1];
cp(pi/4) q[2],q[0];
cp(pi/2) q[1],q[0];
h q[0];
rz(0.05983559455713557) q[2];
swap q[0],q[2];
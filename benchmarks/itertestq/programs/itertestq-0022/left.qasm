OPENQASM 2.0;
include "qelib1.inc";
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
qreg qr[11];
creg cr[11];
ry(2.55575) qr[1];
cs qr[1],qr[8];
cy qr[2],qr[1];
ccz qr[3],qr[8],qr[2];
cu(2.432646,-pi/2,pi/2,0) qr[3],qr[10];
cx qr[4],qr[2];
ry(1.027374) qr[6];
cy qr[4],qr[5];
cp(0.49761) qr[9],qr[1];
ryy(0.127256) qr[5],qr[2];
h qr[2];
cry(1.007401) qr[10],qr[8];
rx(5.474927) qr[0];
barrier qr[6],qr[5],qr[4],qr[8];
cp(4.017117) qr[2],qr[7];

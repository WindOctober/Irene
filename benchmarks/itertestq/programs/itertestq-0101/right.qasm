OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate unitary q0 { u(0,-0.6684700000000001,-0.6684700000000001) q0; }
gate unitary_140319934868368 q0 { u(0,-2.473122653589793,3.8100626535897932) q0; }
gate unitary_140319934868032 q0 { u(0,-2.473122653589793,3.8100626535897932) q0; }
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
qreg qr[11];
creg cr[11];
cu(2.82009,2.745822,4.29971,2.318459) qr[0],qr[8];
csx qr[9],qr[7];
ry(2.4289525) qr[4];
cx qr[10],qr[4];
ry(-2.4289525) qr[4];
cx qr[10],qr[4];
csx qr[4],qr[9];
rx(4.876591) qr[10];
ecr qr[6],qr[8];
rcccx qr[0],qr[6],qr[10],qr[5];
sdg qr[7];
ry(2.41819) qr[0];
cx qr[10],qr[0];
ry(-2.41819) qr[0];
cx qr[10],qr[0];
sdg qr[9];
ccx qr[1],qr[0],qr[3];
unitary qr[3];
cx qr[9],qr[3];
unitary_140319934868368 qr[3];
ccx qr[1],qr[0],qr[3];
unitary qr[3];
cx qr[9],qr[3];
unitary_140319934868032 qr[3];
r(1.069971,2.869223) qr[2];
rxx(0.615779) qr[4],qr[3];
crx(4.957727) qr[1],qr[9];
cswap qr[1],qr[2],qr[5];

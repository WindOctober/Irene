OPENQASM 2.0;
include "qelib1.inc";
gate r(param0,param1) q0 { u3(1.069971,1.2984266732051033,-1.2984266732051033) q0; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(pi/4) q1; cx q0,q1; h q1; }
gate rzx_139980528285152(param0) q0,q1 { h q1; cx q0,q1; rz(-pi/4) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx_139980528285152(-pi/4) q0,q1; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate unitary_140319934868368 q0 { u(0,-2.473122653589793,3.8100626535897932) q0; }
gate unitary_140319934868032 q0 { u(0,-2.473122653589793,3.8100626535897932) q0; }
qreg qr[11];
creg cr[11];
r(1.069971,2.869223) qr[2];
ry(2.4289525) qr[4];
cu(2.82009,2.745822,4.29971,2.318459) qr[0],qr[8];
ecr qr[6],qr[8];
csx qr[9],qr[7];
sdg qr[7];
cx qr[10],qr[4];
ry(-2.4289525) qr[4];
cx qr[10],qr[4];
rx(4.876591) qr[10];
rcccx qr[0],qr[6],qr[10],qr[5];
ry(2.41819) qr[0];
cx qr[10],qr[0];
ry(-2.41819) qr[0];
cx qr[10],qr[0];
ccx qr[1],qr[0],qr[3];
u3(0,0,-1.3369400000000002) qr[3];
csx qr[4],qr[9];
sdg qr[9];
cx qr[9],qr[3];
unitary_140319934868368 qr[3];
ccx qr[1],qr[0],qr[3];
u3(0,0,-1.3369400000000002) qr[3];
cx qr[9],qr[3];
crx(4.957727) qr[1],qr[9];
cswap qr[1],qr[2],qr[5];
unitary_140319934868032 qr[3];
rxx(0.615779) qr[4],qr[3];

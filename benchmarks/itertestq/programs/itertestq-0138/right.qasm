OPENQASM 2.0;
include "qelib1.inc";
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
qreg qr[11];
creg cr[11];
rccx qr[4],qr[8],qr[1];
cswap qr[6],qr[5],qr[1];
s qr[7];
cs qr[2],qr[0];
ccx qr[9],qr[2],qr[0];
cry(0.092577) qr[0],qr[1];
rzz(5.255324) qr[9],qr[1];
rxx(1.248268) qr[3],qr[6];
crx(0.628867) qr[7],qr[9];
ccz qr[4],qr[9],qr[5];
rcccx qr[4],qr[10],qr[2],qr[1];
rzx(2.586159) qr[6],qr[7];
dcx qr[8],qr[2];
cu(0.6750775,0,0,0) qr[7],qr[0];
cx qr[7],qr[8];
cu(-0.6750775,0,0,0) qr[8],qr[0];
cx qr[7],qr[8];
cu(0.6750775,0,0,0) qr[8],qr[0];
cx qr[8],qr[4];
cu(-0.6750775,0,0,0) qr[4],qr[0];
cx qr[7],qr[4];
cu(0.6750775,0,0,0) qr[4],qr[0];
cx qr[8],qr[4];
cu(-0.6750775,0,0,0) qr[4],qr[0];
cx qr[7],qr[4];
cu(0.6750775,0,0,0) qr[4],qr[0];
ecr qr[6],qr[2];

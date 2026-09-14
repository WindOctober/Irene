OPENQASM 2.0;
include "qelib1.inc";
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
qreg qr[11];
creg cr[11];
cu(1.0990825,-pi/2,pi/2,0) qr[7],qr[0];
cx qr[7],qr[2];
cu(-1.0990825,-pi/2,pi/2,0) qr[2],qr[0];
cx qr[7],qr[2];
cu(1.0990825,-pi/2,pi/2,0) qr[2],qr[0];
h qr[4];
h qr[9];
crx(0.240182) qr[2],qr[0];
cz qr[0],qr[1];
rx(1.880587) qr[7];
rcccx qr[8],qr[0],qr[5],qr[2];
cp(1.373946) qr[9],qr[4];
crx(2.67796) qr[8],qr[3];
cu(0.69717025,-pi/2,pi/2,0) qr[7],qr[8];
cx qr[7],qr[10];
cu(-0.69717025,-pi/2,pi/2,0) qr[10],qr[8];
cx qr[7],qr[10];
cu(0.69717025,-pi/2,pi/2,0) qr[10],qr[8];
cx qr[10],qr[2];
cu(-0.69717025,-pi/2,pi/2,0) qr[2],qr[8];
cx qr[7],qr[2];
cu(0.69717025,-pi/2,pi/2,0) qr[2],qr[8];
cx qr[10],qr[2];
cu(-0.69717025,-pi/2,pi/2,0) qr[2],qr[8];
cx qr[7],qr[2];
cu(0.69717025,-pi/2,pi/2,0) qr[2],qr[8];
rzx(3.80319) qr[2],qr[7];
ecr qr[0],qr[5];
id qr[7];
cx qr[6],qr[8];
cp(0.220809) qr[2],qr[8];

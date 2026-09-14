OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate mcx q0,q1,q2,q3 { h q3; p(pi/8) q0; p(pi/8) q1; p(pi/8) q2; p(pi/8) q3; cx q0,q1; p(-pi/8) q1; cx q0,q1; cx q1,q2; p(-pi/8) q2; cx q0,q2; p(pi/8) q2; cx q1,q2; p(-pi/8) q2; cx q0,q2; cx q2,q3; p(-pi/8) q3; cx q1,q3; p(pi/8) q3; cx q2,q3; p(-pi/8) q3; cx q0,q3; p(pi/8) q3; cx q2,q3; p(-pi/8) q3; cx q1,q3; p(pi/8) q3; cx q2,q3; p(-pi/8) q3; cx q0,q3; h q3; }
gate mcx_140168487597968 q0,q1,q2,q3 { mcx q0,q1,q2,q3; }
qreg qr[11];
creg cr[11];
cx qr[10],qr[1];
ecr qr[10],qr[6];
swap qr[4],qr[6];
mcx_140168487597968 qr[3],qr[0],qr[4],qr[2];
csx qr[3],qr[4];
s qr[3];
ccx qr[10],qr[1],qr[2];
rz(4.671996) qr[9];
rzz(3.827033) qr[1],qr[10];
rzx(4.477186) qr[7],qr[0];
p(1.848654) qr[1];
sdg qr[9];
ry(5.222081) qr[8];
cz qr[1],qr[8];
h qr[1];

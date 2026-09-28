OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(2.977089) q1; cx q0,q1; h q1; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
qreg qr[11];
creg cr[11];
s qr[1];
ry(1.569383) qr[3];
cz qr[1],qr[3];
rzx(2.977089) qr[1],qr[5];
cp(1.899192) qr[4],qr[7];
cry(0.866048) qr[0],qr[4];
p(3.979449) qr[0];
barrier qr[2],qr[4];
ccz qr[8],qr[3],qr[1];
cx qr[6],qr[9];
swap qr[2],qr[6];
cz qr[6],qr[2];
rzz(0.268262) qr[9],qr[4];
swap qr[10],qr[0];
rzz(1.613376) qr[10],qr[0];

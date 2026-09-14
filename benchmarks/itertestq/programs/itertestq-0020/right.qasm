OPENQASM 2.0;
include "qelib1.inc";
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
qreg qr[11];
creg cr[11];
sdg qr[8];
cry(0.226041) qr[10],qr[2];
cry(2.660996) qr[7],qr[3];
ccz qr[6],qr[3],qr[1];
ecr qr[9],qr[10];
barrier qr[10],qr[7];
ecr qr[9],qr[10];
crx(0.895119) qr[6],qr[1];
rzz(3.38333) qr[3],qr[7];
cp(2.749971) qr[10],qr[5];
cy qr[6],qr[1];
ry(0.4209335) qr[7];
cx qr[10],qr[7];
ry(-0.4209335) qr[7];
cx qr[10],qr[7];
rzx(3.006624) qr[0],qr[1];
ry(5.535363) qr[9];
cu(2.206976,0.472194,2.123819,2.831601) qr[2],qr[0];

OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
qreg qr[11];
creg cr[11];
swap qr[8],qr[4];
cry(3.811192) qr[6],qr[9];
rxx(1.845845) qr[9],qr[3];
cu(3.981434,2.45052,2.042675,5.511318) qr[3],qr[0];
csx qr[9],qr[6];
cz qr[3],qr[1];
cx qr[6],qr[10];
cu(0.870554,-pi/2,pi/2,0) qr[5],qr[2];
ecr qr[10],qr[8];
dcx qr[10],qr[3];
cu(0.8155315,-pi/2,pi/2,0) qr[3],qr[2];
cx qr[3],qr[5];
cu(-0.8155315,-pi/2,pi/2,0) qr[5],qr[2];
cx qr[3],qr[5];
cu(0.8155315,-pi/2,pi/2,0) qr[5],qr[2];
cx qr[5],qr[7];
cu(-0.8155315,-pi/2,pi/2,0) qr[7],qr[2];
cx qr[3],qr[7];
cu(0.8155315,-pi/2,pi/2,0) qr[7],qr[2];
cx qr[5],qr[7];
cu(-0.8155315,-pi/2,pi/2,0) qr[7],qr[2];
cx qr[3],qr[7];
cu(0.8155315,-pi/2,pi/2,0) qr[7],qr[2];
rzx(5.687108) qr[2],qr[0];
swap qr[1],qr[10];
ecr qr[6],qr[3];
cry(0.890943) qr[1],qr[9];

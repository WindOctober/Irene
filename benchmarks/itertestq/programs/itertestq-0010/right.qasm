OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate mcphase(param0) q0,q1 { cp(2.98334) q0,q1; }
qreg qr[11];
creg cr[11];
swap qr[0],qr[3];
cswap qr[4],qr[10],qr[5];
ccx qr[6],qr[7],qr[0];
ecr qr[4],qr[6];
p(2.041536) qr[1];
rxx(2.947491) qr[2],qr[7];
ecr qr[0],qr[2];
ryy(3.373405) qr[0],qr[10];
cswap qr[7],qr[9],qr[3];
cry(3.701291) qr[10],qr[8];
cz qr[4],qr[1];
rcccx qr[4],qr[1],qr[10],qr[8];
ryy(2.852053) qr[4],qr[2];
mcphase(2.98334) qr[8],qr[5];
cu(1.35997275,-pi/2,pi/2,0) qr[3],qr[1];
cx qr[3],qr[8];
cu(-1.35997275,-pi/2,pi/2,0) qr[8],qr[1];
cx qr[3],qr[8];
cu(1.35997275,-pi/2,pi/2,0) qr[8],qr[1];
cx qr[8],qr[5];
cu(-1.35997275,-pi/2,pi/2,0) qr[5],qr[1];
cx qr[3],qr[5];
cu(1.35997275,-pi/2,pi/2,0) qr[5],qr[1];
cx qr[8],qr[5];
cu(-1.35997275,-pi/2,pi/2,0) qr[5],qr[1];
cx qr[3],qr[5];
cu(1.35997275,-pi/2,pi/2,0) qr[5],qr[1];

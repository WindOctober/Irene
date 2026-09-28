OPENQASM 2.0;
include "qelib1.inc";
gate rv(param0,param1,param2) q0 { u(0.46038467315702025,-0.5186448007752631,0.5730223200926643) q0; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate mcphase(param0) q0,q1 { cp(4.003059) q0,q1; }
qreg qr[11];
creg cr[11];
id qr[7];
ry(3.00308) qr[0];
cry(6.203148) qr[2],qr[0];
cy qr[5],qr[4];
cx qr[3],qr[6];
cz qr[4],qr[1];
cy qr[8],qr[4];
s qr[10];
rv(3.479095,5.727969,0.777441) qr[1];
rcccx qr[6],qr[4],qr[7],qr[8];
cy qr[9],qr[2];
ccx qr[10],qr[3],qr[4];
barrier qr[2],qr[0],qr[1],qr[5];
h qr[8];
mcphase(4.003059) qr[4],qr[6];

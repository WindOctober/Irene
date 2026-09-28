OPENQASM 2.0;
include "qelib1.inc";
gate csdg q0,q1 { p(-pi/4) q0; cx q0,q1; p(pi/4) q1; cx q0,q1; p(-pi/4) q1; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
qreg qr[11];
creg cr[11];
h qr[8];
csdg qr[4],qr[5];
cp(3.588381) qr[4],qr[10];
cp(0.025466) qr[3],qr[9];
crx(1.469617) qr[4],qr[7];
rccx qr[0],qr[10],qr[1];
rcccx qr[4],qr[5],qr[0],qr[10];
cu(0.658558,4.282199,6.07362,0.547271) qr[10],qr[5];
cu(0.561125,3.230334,4.301281,1.35738) qr[2],qr[8];
sdg qr[3];
ccz qr[2],qr[4],qr[10];
p(0.247209) qr[6];
barrier qr[9],qr[0];
rcccx qr[5],qr[4],qr[9],qr[3];
id qr[3];

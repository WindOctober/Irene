OPENQASM 2.0;
include "qelib1.inc";
gate rv(param0,param1,param2) q0 { u(1.3837448691693677,-0.623776601349868,1.7395729095577943) q0; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
qreg qr[11];
creg cr[11];
rv(6.238004,2.557759,4.308149) qr[9];
crz(3.277764) qr[1],qr[8];
sdg qr[2];
crx(3.441221) qr[0],qr[5];
cp(1.168123) qr[5],qr[6];
rzx(0.13168) qr[5],qr[6];
csx qr[8],qr[2];
barrier qr[8],qr[2];
ry(4.533605) qr[9];
rcccx qr[5],qr[7],qr[4],qr[9];
r(4.894615,4.980323) qr[1];
s qr[10];
rccx qr[8],qr[5],qr[0];
rzz(1.669356) qr[2],qr[1];
rz(6.052042) qr[7];

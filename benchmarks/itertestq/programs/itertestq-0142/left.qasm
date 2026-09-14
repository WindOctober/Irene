OPENQASM 2.0;
include "qelib1.inc";
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
qreg qr[11];
creg cr[11];
r(6.06423,4.077973) qr[9];
rxx(0.724951) qr[9],qr[6];
cy qr[4],qr[9];
rzz(1.701339) qr[4],qr[7];
crz(3.156904) qr[0],qr[4];
crz(0.293031) qr[3],qr[4];
h qr[3];
h qr[6];
cu(2.27327,-pi/2,pi/2,0) qr[6],qr[8];
cx qr[6],qr[0];
cu(-2.27327,-pi/2,pi/2,0) qr[0],qr[8];
cx qr[6],qr[0];
cu(2.27327,-pi/2,pi/2,0) qr[0],qr[8];
rcccx qr[6],qr[0],qr[2],qr[7];
r(0.725428,5.091691) qr[6];
ryy(0.533026) qr[1],qr[0];
rzx(3.242289) qr[2],qr[0];
csx qr[4],qr[6];
dcx qr[1],qr[2];

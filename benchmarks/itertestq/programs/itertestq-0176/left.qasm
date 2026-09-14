OPENQASM 2.0;
include "qelib1.inc";
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate rv(param0,param1,param2) q0 { u(0.038108179281934024,2.8168605851865376,-2.8373007369834733) q0; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
qreg qr[11];
creg cr[11];
r(6.110834,1.061872) qr[5];
swap qr[0],qr[1];
rx(6.013272) qr[1];
cz qr[0],qr[10];
barrier qr[5],qr[3];
rccx qr[1],qr[5],qr[6];
rx(2.343233) qr[7];
r(0.018461,3.107887) qr[0];
ryy(1.806411) qr[4],qr[9];
crz(6.089329) qr[4],qr[6];
ccx qr[8],qr[10],qr[6];
ccx qr[3],qr[6],qr[8];
rv(1.701144,5.229306,2.949126) qr[10];
cs qr[2],qr[7];
rzx(0.84432) qr[2],qr[5];

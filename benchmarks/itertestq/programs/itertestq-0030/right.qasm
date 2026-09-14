OPENQASM 2.0;
include "qelib1.inc";
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
gate rv(param0,param1,param2) q0 { u(2.1931644579930394,1.8309280651251996,-2.978270121179391) q0; }
qreg qr[11];
creg cr[11];
rcccx qr[8],qr[0],qr[1],qr[7];
cs qr[7],qr[10];
cu(4.237206,-pi/2,pi/2,0) qr[10],qr[6];
crx(4.970953) qr[3],qr[5];
cx qr[5],qr[4];
ryy(1.998915) qr[3],qr[0];
dcx qr[0],qr[9];
r(3.676998,4.698967) qr[0];
cu(0.921279,-pi/2,pi/2,0) qr[7],qr[0];
cx qr[7],qr[6];
cu(-0.921279,-pi/2,pi/2,0) qr[6],qr[0];
cx qr[7],qr[6];
cu(0.921279,-pi/2,pi/2,0) qr[6],qr[0];
cx qr[6],qr[3];
cu(-0.921279,-pi/2,pi/2,0) qr[3],qr[0];
cx qr[7],qr[3];
cu(0.921279,-pi/2,pi/2,0) qr[3],qr[0];
cx qr[6],qr[3];
cu(-0.921279,-pi/2,pi/2,0) qr[3],qr[0];
cx qr[7],qr[3];
cu(0.921279,-pi/2,pi/2,0) qr[3],qr[0];
id qr[5];
r(1.348708,0.158591) qr[5];
rv(2.543589,2.80257,1.0543) qr[8];
cswap qr[7],qr[1],qr[6];
cu(1.1164615,-pi/2,pi/2,0) qr[8],qr[7];
cx qr[8],qr[9];
cu(-1.1164615,-pi/2,pi/2,0) qr[9],qr[7];
cx qr[8],qr[9];
cu(1.1164615,-pi/2,pi/2,0) qr[9],qr[7];
cx qr[9],qr[3];
cu(-1.1164615,-pi/2,pi/2,0) qr[3],qr[7];
cx qr[8],qr[3];
cu(1.1164615,-pi/2,pi/2,0) qr[3],qr[7];
cx qr[9],qr[3];
cu(-1.1164615,-pi/2,pi/2,0) qr[3],qr[7];
cx qr[8],qr[3];
cu(1.1164615,-pi/2,pi/2,0) qr[3],qr[7];
s qr[0];

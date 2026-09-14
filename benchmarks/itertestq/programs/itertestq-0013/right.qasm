OPENQASM 2.0;
include "qelib1.inc";
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(4.069753) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(pi/4) q1; cx q0,q1; h q1; }
gate rzx_139628650539152(param0) q0,q1 { h q1; cx q0,q1; rz(-pi/4) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx_139628650539152(-pi/4) q0,q1; }
gate mcphase(param0) q0,q1,q2,q3 { u(pi/2,0,pi) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-0.016567499999999846,-3*pi/4) q3; cx q2,q3; u(pi/2,0,-3.1250251535897924) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-0.016567499999999846,-3*pi/4) q3; cx q2,q3; u(0,-3.133308903589793,-3.1333089035897927) q3; cx q0,q2; u(0,-0.004141875000000184,-0.004141875000000184) q2; cx q1,q2; u(0,-3.137450778589793,-3.137450778589793) q2; cx q0,q2; u(0,-0.004141875000000184,-0.004141875000000184) q2; cx q1,q2; u(0,-3.137450778589793,-3.137450778589793) q2; u(0,0,0.00828375) q1; cx q0,q1; u(0,0,-0.00828375) q1; cx q0,q1; p(0.00828375) q0; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
qreg qr[11];
creg cr[11];
swap qr[8],qr[6];
ryy(4.069753) qr[4],qr[6];
h qr[6];
cs qr[6],qr[2];
ecr qr[9],qr[7];
cry(3.847725) qr[7],qr[3];
crz(3.26731) qr[9],qr[0];
cz qr[0],qr[7];
cy qr[10],qr[1];
ry(1.924628) qr[10];
cx qr[9],qr[10];
ry(-1.924628) qr[10];
cx qr[9],qr[10];
cy qr[3],qr[10];
mcphase(0.06627) qr[7],qr[9],qr[1],qr[8];
cp(0.21664) qr[7],qr[9];
rcccx qr[7],qr[2],qr[1],qr[4];
ccz qr[2],qr[6],qr[8];

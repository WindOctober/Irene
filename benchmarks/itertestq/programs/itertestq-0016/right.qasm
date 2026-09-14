OPENQASM 2.0;
include "qelib1.inc";
gate unitary q0 { u(0,-0.68420625,-0.68420625) q0; }
gate unitary_140168493642176 q0 { u(0,-2.457386403589793,3.825798903589793) q0; }
gate unitary_140168487896352 q0 { u(0,-2.457386403589793,3.825798903589793) q0; }
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
gate rv(param0,param1,param2) q0 { u(0.01594990827177066,-1.2125407274527975,1.2370508721871483) q0; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
qreg qr[11];
creg cr[11];
ccx qr[7],qr[10],qr[0];
cy qr[5],qr[9];
sdg qr[6];
ry(1.385168) qr[6];
cu(0.092975,0.800751,3.667294,3.786285) qr[10],qr[9];
swap qr[10],qr[9];
ccx qr[1],qr[5],qr[6];
ccx qr[3],qr[7],qr[8];
unitary qr[8];
cx qr[2],qr[8];
unitary_140168493642176 qr[8];
ccx qr[3],qr[7],qr[8];
unitary qr[8];
cx qr[2],qr[8];
unitary_140168487896352 qr[8];
r(1.360259,0.204476) qr[9];
cx qr[0],qr[4];
rzz(3.285739) qr[7],qr[9];
cx qr[3],qr[1];
rv(3.239041,1.167683,5.290735) qr[0];
cy qr[2],qr[4];
ecr qr[10],qr[8];

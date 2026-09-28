OPENQASM 2.0;
include "qelib1.inc";
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate csdg q0,q1 { p(-pi/4) q0; cx q0,q1; p(pi/4) q1; cx q0,q1; p(-pi/4) q1; }
gate iswap q0,q1 { s q0; s q1; h q0; cx q0,q1; cx q1,q0; h q1; }
qreg qr[11];
creg cr[11];
cu(0.10891025,0,0,0) qr[3],qr[0];
cx qr[3],qr[9];
cu(-0.10891025,0,0,0) qr[9],qr[0];
cx qr[3],qr[9];
cu(0.10891025,0,0,0) qr[9],qr[0];
cx qr[9],qr[2];
cu(-0.10891025,0,0,0) qr[2],qr[0];
cx qr[3],qr[2];
cu(0.10891025,0,0,0) qr[2],qr[0];
cx qr[9],qr[2];
cu(-0.10891025,0,0,0) qr[2],qr[0];
cx qr[3],qr[2];
cu(0.10891025,0,0,0) qr[2],qr[0];
cy qr[2],qr[6];
cswap qr[3],qr[5],qr[0];
s qr[5];
cp(6.230241) qr[8],qr[3];
cs qr[9],qr[0];
ecr qr[4],qr[5];
cy qr[9],qr[10];
cry(6.172107) qr[10],qr[4];
csdg qr[0],qr[3];
sdg qr[6];
cswap qr[8],qr[5],qr[10];
iswap qr[3],qr[4];
csx qr[9],qr[5];
ry(5.099964) qr[3];

OPENQASM 2.0;
include "qelib1.inc";
gate mcphase(param0) q0,q1,q2 { cx q0,q2; u(0,-0.07937387499999993,-0.07937387499999993) q2; cx q1,q2; u(0,-3.062218778589793,-3.062218778589793) q2; cx q0,q2; u(0,-0.07937387499999993,-0.07937387499999993) q2; cx q1,q2; u(0,-3.062218778589793,-3.062218778589793) q2; u(0,0,0.15874775) q1; cx q0,q1; u(0,0,-0.15874775) q1; cx q0,q1; p(0.15874775) q0; }
gate mcx q0,q1,q2,q3 { h q3; p(pi/8) q0; p(pi/8) q1; p(pi/8) q2; p(pi/8) q3; cx q0,q1; p(-pi/8) q1; cx q0,q1; cx q1,q2; p(-pi/8) q2; cx q0,q2; p(pi/8) q2; cx q1,q2; p(-pi/8) q2; cx q0,q2; cx q2,q3; p(-pi/8) q3; cx q1,q3; p(pi/8) q3; cx q2,q3; p(-pi/8) q3; cx q0,q3; p(pi/8) q3; cx q2,q3; p(-pi/8) q3; cx q1,q3; p(pi/8) q3; cx q2,q3; p(-pi/8) q3; cx q0,q3; h q3; }
gate mcx_140168486864640 q0,q1,q2,q3 { mcx q0,q1,q2,q3; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
qreg qr[11];
creg cr[11];
mcphase(0.634991) qr[1],qr[4],qr[2];
barrier qr[3];
mcx_140168486864640 qr[4],qr[6],qr[8],qr[3];
sdg qr[8];
id qr[10];
dcx qr[2],qr[4];
rz(4.254984) qr[8];
cu(5.220958,0.908908,1.641774,5.449565) qr[4],qr[1];
cp(5.297149) qr[7],qr[9];
ecr qr[3],qr[8];
cp(3.107023) qr[2],qr[0];
cswap qr[2],qr[0],qr[9];
cp(1.219203) qr[0],qr[3];
ry(2.811279) qr[2];
ryy(1.066357) qr[10],qr[5];

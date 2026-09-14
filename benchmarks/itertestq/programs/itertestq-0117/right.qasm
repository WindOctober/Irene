OPENQASM 2.0;
include "qelib1.inc";
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate mcphase(param0) q0,q1,q2,q3 { u(pi/2,0,pi) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-1.562608499999997,-3*pi/4) q3; cx q2,q3; u(pi/2,0,-1.578984153589797) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-1.562608499999997,-3*pi/4) q3; cx q2,q3; u(0,-2.3602884035897946,-2.360288403589795) q3; cx q0,q2; u(0,-0.3906521249999999,-0.3906521249999999) q2; cx q1,q2; u(0,-2.750940528589793,-2.750940528589793) q2; cx q0,q2; u(0,-0.3906521249999999,-0.3906521249999999) q2; cx q1,q2; u(0,-2.750940528589793,-2.750940528589793) q2; u(0,0,0.78130425) q1; cx q0,q1; u(0,0,-0.78130425) q1; cx q0,q1; p(0.78130425) q0; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
gate iswap q0,q1 { s q0; s q1; h q0; cx q0,q1; cx q1,q0; h q1; }
qreg qr[11];
creg cr[11];
h qr[4];
ryy(6.048849) qr[0],qr[8];
ecr qr[0],qr[9];
cu(2.22169,4.14421,3.242857,1.874554) qr[1],qr[4];
mcphase(6.250434) qr[4],qr[0],qr[5],qr[2];
rzx(2.713859) qr[2],qr[3];
cu(0.8241455,-pi/2,pi/2,0) qr[7],qr[5];
cx qr[7],qr[4];
cu(-0.8241455,-pi/2,pi/2,0) qr[4],qr[5];
cx qr[7],qr[4];
cu(0.8241455,-pi/2,pi/2,0) qr[4],qr[5];
cx qr[4],qr[10];
cu(-0.8241455,-pi/2,pi/2,0) qr[10],qr[5];
cx qr[7],qr[10];
cu(0.8241455,-pi/2,pi/2,0) qr[10],qr[5];
cx qr[4],qr[10];
cu(-0.8241455,-pi/2,pi/2,0) qr[10],qr[5];
cx qr[7],qr[10];
cu(0.8241455,-pi/2,pi/2,0) qr[10],qr[5];
cu(2.351994,4.95124,1.416776,6.154363) qr[0],qr[1];
crx(3.901196) qr[1],qr[5];
sdg qr[5];
ccz qr[7],qr[2],qr[10];
cy qr[4],qr[5];
cy qr[6],qr[2];
iswap qr[1],qr[2];
rzz(4.810512) qr[5],qr[9];

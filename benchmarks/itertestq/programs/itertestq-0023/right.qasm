OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate rv(param0,param1,param2) q0 { u(0.5450251595010823,2.012470424918641,-2.4384347035916463) q0; }
gate mcphase(param0) q0,q1,q2 { cx q0,q2; u(0,-0.29019812499999986,-0.29019812499999986) q2; cx q1,q2; u(0,-2.8513945285897933,-2.8513945285897933) q2; cx q0,q2; u(0,-0.29019812499999986,-0.29019812499999986) q2; cx q1,q2; u(0,-2.8513945285897933,-2.8513945285897933) q2; u(0,0,0.58039625) q1; cx q0,q1; u(0,0,-0.58039625) q1; cx q0,q1; p(0.58039625) q0; }
gate r(param0,param1) q0 { u3(param0,param1 - pi/2,pi/2 - param1) q0; }
qreg qr[11];
creg cr[11];
cu(1.58121,1.679866,4.596579,4.456842) qr[6],qr[8];
cswap qr[1],qr[0],qr[4];
swap qr[4],qr[3];
swap qr[10],qr[2];
ecr qr[4],qr[1];
rv(3.539617,2.716931,3.374967) qr[7];
cu(0.504075,0,0,0) qr[2],qr[7];
cx qr[2],qr[9];
cu(-0.504075,0,0,0) qr[9],qr[7];
cx qr[2],qr[9];
cu(0.504075,0,0,0) qr[9],qr[7];
cx qr[9],qr[6];
cu(-0.504075,0,0,0) qr[6],qr[7];
cx qr[2],qr[6];
cu(0.504075,0,0,0) qr[6],qr[7];
cx qr[9],qr[6];
cu(-0.504075,0,0,0) qr[6],qr[7];
cx qr[2],qr[6];
cu(0.504075,0,0,0) qr[6],qr[7];
cz qr[0],qr[4];
cx qr[8],qr[3];
csx qr[10],qr[2];
mcphase(2.321585) qr[4],qr[6],qr[2];
cx qr[1],qr[7];
crx(1.531147) qr[10],qr[0];
r(4.905934,3.765186) qr[3];
cu(2.091508,-pi/2,pi/2,0) qr[5],qr[1];
cx qr[5],qr[0];
cu(-2.091508,-pi/2,pi/2,0) qr[0],qr[1];
cx qr[5],qr[0];
cu(2.091508,-pi/2,pi/2,0) qr[0],qr[1];

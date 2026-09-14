OPENQASM 2.0;
include "qelib1.inc";
gate csdg q0,q1 { p(-pi/4) q0; cx q0,q1; p(pi/4) q1; cx q0,q1; p(-pi/4) q1; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
qreg qr[11];
creg cr[11];
rzz(0.098986) qr[4],qr[10];
csdg qr[3],qr[0];
cu(2.724217,-pi/2,pi/2,0) qr[0],qr[2];
cx qr[0],qr[4];
cu(-2.724217,-pi/2,pi/2,0) qr[4],qr[2];
cx qr[0],qr[4];
cu(2.724217,-pi/2,pi/2,0) qr[4],qr[2];
p(2.969073) qr[4];
ccx qr[2],qr[6],qr[8];
s qr[8];
crz(3.576876) qr[0],qr[7];
ry(2.075473) qr[7];
cx qr[5],qr[7];
ry(-2.075473) qr[7];
cx qr[5],qr[7];
cp(1.279098) qr[10],qr[5];
crz(0.083149) qr[8],qr[7];
rx(4.646293) qr[2];
cry(3.714171) qr[5],qr[7];
rz(4.856449) qr[2];
ryy(2.2364) qr[0],qr[7];
crz(0.194165) qr[9],qr[6];

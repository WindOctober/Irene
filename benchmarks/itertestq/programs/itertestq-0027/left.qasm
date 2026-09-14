OPENQASM 2.0;
include "qelib1.inc";
gate csdg q0,q1 { p(-pi/4) q0; cx q0,q1; p(pi/4) q1; cx q0,q1; p(-pi/4) q1; }
gate mcphase(param0) q0,q1 { cp(5.964846) q0,q1; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
qreg qr[11];
creg cr[11];
csdg qr[3],qr[9];
cz qr[1],qr[7];
sdg qr[5];
id qr[7];
csx qr[2],qr[3];
mcphase(5.964846) qr[4],qr[5];
crz(2.035115) qr[0],qr[5];
rz(3.551617) qr[10];
crx(1.488079) qr[2],qr[4];
csx qr[7],qr[9];
cx qr[4],qr[8];
cx qr[8],qr[1];
cu(3.151042,6.091474,6.147223,5.039554) qr[7],qr[4];
cx qr[1],qr[8];
ryy(4.889218) qr[10],qr[5];

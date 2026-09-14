OPENQASM 2.0;
include "qelib1.inc";
gate iswap q0,q1 { s q0; s q1; h q0; cx q0,q1; cx q1,q0; h q1; }
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate mcphase(param0) q0,q1,q2,q3 { u(pi/2,0,pi) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-0.9028214999999999,-3*pi/4) q3; cx q2,q3; u(pi/2,0,-2.238771153589793) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-0.9028214999999999,-3*pi/4) q3; cx q2,q3; u(0,-2.690181903589793,-2.690181903589793) q3; cx q0,q2; u(0,-0.22570537499999999,-0.22570537499999999) q2; cx q1,q2; u(0,-2.915887278589793,-2.9158872785897927) q2; cx q0,q2; u(0,-0.22570537499999999,-0.22570537499999999) q2; cx q1,q2; u(0,-2.915887278589793,-2.9158872785897927) q2; u(0,0,0.45141075) q1; cx q0,q1; u(0,0,-0.45141075) q1; cx q0,q1; p(0.45141075) q0; }
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
gate mcphase_140168494259248(param0) q0,q1,q2,q3 { u(pi/2,0,pi) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-1.2763150000000008,-3*pi/4) q3; cx q2,q3; u(pi/2,0,-1.8652776535897928) q3; cx q1,q3; p(-pi/4) q3; cx q0,q3; p(pi/4) q3; cx q1,q3; p(pi/4) q1; p(-pi/4) q3; cx q0,q3; cx q0,q1; p(pi/4) q0; p(-pi/4) q1; cx q0,q1; u(pi/2,-1.2763150000000008,-3*pi/4) q3; cx q2,q3; u(0,-2.503435153589793,-2.503435153589793) q3; cx q0,q2; u(0,-0.3190787500000001,-0.3190787500000001) q2; cx q1,q2; u(0,-2.822513903589793,-2.822513903589793) q2; cx q0,q2; u(0,-0.3190787500000001,-0.3190787500000001) q2; cx q1,q2; u(0,-2.822513903589793,-2.822513903589793) q2; u(0,0,0.6381575) q1; cx q0,q1; u(0,0,-0.6381575) q1; cx q0,q1; p(0.6381575) q0; }
qreg qr[11];
creg cr[11];
id qr[9];
iswap qr[6],qr[2];
rx(2.069552) qr[2];
rzx(5.924631) qr[10],qr[3];
rx(2.146706) qr[5];
crz(4.128895) qr[8],qr[5];
rzz(3.760935) qr[4],qr[0];
mcphase(3.611286) qr[0],qr[10],qr[2],qr[1];
rcccx qr[6],qr[8],qr[0],qr[9];
cs qr[2],qr[9];
dcx qr[0],qr[1];
mcphase_140168494259248(5.10526) qr[5],qr[0],qr[6],qr[3];
cu(4.654683,4.259876,5.72911,3.479805) qr[1],qr[2];
iswap qr[10],qr[0];
rcccx qr[2],qr[4],qr[8],qr[7];

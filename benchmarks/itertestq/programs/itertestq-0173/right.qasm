OPENQASM 2.0;
include "qelib1.inc";
gate rcccx q0,q1,q2,q3 { u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; u2(0,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(0,pi) q3; }
gate rcccx_dg q0,q1,q2,q3 { u2(-2*pi,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(-2*pi,pi) q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u1(pi/4) q3; cx q1,q3; u1(-pi/4) q3; cx q0,q3; u2(-2*pi,pi) q3; u1(pi/4) q3; cx q2,q3; u1(-pi/4) q3; u2(-2*pi,pi) q3; }
gate mcx q0,q1,q2,q3,q4 { h q4; cu1(pi/2) q3,q4; h q4; rcccx q0,q1,q2,q3; h q4; cu1(-pi/2) q3,q4; h q4; rcccx_dg q0,q1,q2,q3; c3sqrtx q0,q1,q2,q4; }
qreg q[11];
creg c[11];
crz(3.9187865165696523) q[0],q[9];
mcx q[3],q[1],q[9],q[7],q[8];
crx(2.731697758752422) q[5],q[7];
rccx q[6],q[3],q[2];
sxdg q[3];
cu(2.3200149265481005,3.2248015994729933,4.067755238035616,0.37911734128015095) q[7],q[1];
swap q[1],q[2];
tdg q[7];
rccx q[7],q[1],q[5];
u1(3.41216929735916) q[8];
cy q[9],q[6];
cswap q[9],q[6],q[0];
cx q[1],q[9];
sxdg q[1];
rzz(1.221387759544573) q[8],q[10];

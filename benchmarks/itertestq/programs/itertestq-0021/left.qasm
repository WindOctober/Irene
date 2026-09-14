OPENQASM 2.0;
include "qelib1.inc";
gate unitary_140168486530176 q0 { u(0,-2.597439153589793,3.6857461535897933) q0; }
gate unitary_140168486531280 q0 { u(0,-2.597439153589793,3.6857461535897933) q0; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate rv(param0,param1,param2) q0 { u(0.7364670949828203,-1.0735193898211186,1.4593481021669872) q0; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
gate iswap q0,q1 { s q0; s q1; h q0; cx q0,q1; cx q1,q0; h q1; }
qreg qr[11];
creg cr[11];
cx qr[0],qr[5];
u3(0,0,-1.088307) qr[5];
rxx(2.805501) qr[7],qr[1];
cx qr[1],qr[5];
unitary_140168486530176 qr[5];
cx qr[0],qr[5];
u3(0,0,-1.088307) qr[5];
cx qr[1],qr[5];
unitary_140168486531280 qr[5];
cs qr[4],qr[9];
barrier qr[4],qr[2],qr[1];
p(1.676655) qr[1];
crz(2.186187) qr[1],qr[6];
rzz(4.537013) qr[5],qr[4];
rv(6.075026,1.908304,3.164107) qr[5];
cswap qr[10],qr[7],qr[8];
cz qr[0],qr[10];
ccx qr[7],qr[6],qr[9];
rxx(3.856827) qr[2],qr[6];
ccz qr[5],qr[9],qr[10];
cx qr[8],qr[3];
iswap qr[0],qr[8];

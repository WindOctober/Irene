OPENQASM 2.0;
include "qelib1.inc";
gate rv(param0,param1,param2) q0 { u(2.6730323647942056,0.5617828136945295,1.585796854150722) q0; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
qreg qr[11];
creg cr[11];
rv(1.4,2.491118,0.599482) qr[9];
ry(1.663114) qr[9];
ccx qr[6],qr[4],qr[9];
ry(-1.663114) qr[9];
ccx qr[6],qr[4],qr[9];
rxx(4.734897) qr[0],qr[4];
csx qr[0],qr[1];
sdg qr[10];
rz(4.90302) qr[0];
rx(3.524969) qr[3];
p(2.929441) qr[4];
cu(3.318476,1.990087,2.004142,5.596239) qr[4],qr[0];
ccz qr[6],qr[0],qr[9];
h qr[7];
rxx(5.382072) qr[6],qr[5];
cs qr[7],qr[10];
dcx qr[9],qr[6];
cz qr[5],qr[1];

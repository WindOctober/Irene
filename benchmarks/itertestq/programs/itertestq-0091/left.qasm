OPENQASM 2.0;
include "qelib1.inc";
gate unitary q0 { u(0,-0.47116074999999996,-0.47116074999999996) q0; }
gate unitary_140319939524688 q0 { u(0,-2.670431903589793,3.6127534035897932) q0; }
gate unitary_140319939523536 q0 { u(0,-2.670431903589793,3.6127534035897932) q0; }
gate ryy(param0) q0,q1 { rx(pi/2) q0; rx(pi/2) q1; cx q0,q1; rz(param0) q1; cx q0,q1; rx(-pi/2) q0; rx(-pi/2) q1; }
gate cs q0,q1 { p(pi/4) q0; cx q0,q1; p(-pi/4) q1; cx q0,q1; p(pi/4) q1; }
gate ccz q0,q1,q2 { h q2; ccx q0,q1,q2; h q2; }
qreg qr[11];
creg cr[11];
ccx qr[4],qr[1],qr[3];
unitary qr[3];
cx qr[10],qr[3];
unitary_140319939524688 qr[3];
ccx qr[4],qr[1],qr[3];
unitary qr[3];
cx qr[10],qr[3];
unitary_140319939523536 qr[3];
ryy(3.230297) qr[6],qr[0];
ryy(1.303897) qr[5],qr[2];
cs qr[10],qr[8];
rccx qr[1],qr[3],qr[7];
swap qr[0],qr[8];
ccz qr[4],qr[8],qr[10];
cry(1.630262) qr[6],qr[9];
cx qr[7],qr[0];
cz qr[6],qr[1];
cu(0.919875,2.303081,3.466255,3.897414) qr[5],qr[10];
id qr[6];
cs qr[5],qr[2];
ccz qr[5],qr[4],qr[9];
swap qr[8],qr[3];

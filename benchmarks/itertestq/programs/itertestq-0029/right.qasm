OPENQASM 2.0;
include "qelib1.inc";
gate rzx(param0) q0,q1 { h q1; cx q0,q1; rz(param0) q1; cx q0,q1; h q1; }
gate ecr q0,q1 { rzx(pi/4) q0,q1; x q0; rzx(-pi/4) q0,q1; }
gate dcx q0,q1 { cx q0,q1; cx q1,q0; }
qreg qr[11];
creg cr[11];
ecr qr[5],qr[0];
rzz(5.536973) qr[3],qr[7];
csx qr[4],qr[9];
rz(5.367767) qr[2];
ecr qr[6],qr[1];
dcx qr[8],qr[7];
p(1.665452) qr[1];
rzz(0.31142) qr[4],qr[6];
dcx qr[0],qr[3];
cu(0.622507,0,0,0) qr[8],qr[10];
cx qr[8],qr[9];
cu(-0.622507,0,0,0) qr[9],qr[10];
cx qr[8],qr[9];
cu(0.622507,0,0,0) qr[9],qr[10];
cx qr[9],qr[1];
cu(-0.622507,0,0,0) qr[1],qr[10];
cx qr[8],qr[1];
cu(0.622507,0,0,0) qr[1],qr[10];
cx qr[9],qr[1];
cu(-0.622507,0,0,0) qr[1],qr[10];
cx qr[8],qr[1];
cu(0.622507,0,0,0) qr[1],qr[10];
rxx(4.559243) qr[8],qr[9];
crx(4.562017) qr[0],qr[2];
rzx(5.611433) qr[6],qr[2];
crz(0.465773) qr[3],qr[10];
ry(0.393905) qr[10];

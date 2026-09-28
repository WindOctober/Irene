OPENQASM 3.0;
include "stdgates.inc";
bit[5] c;
qubit[100] q;
rz(pi/2) q[93];
cz q[74], q[63];
cx q[20], q[38];
cx q[6], q[19];
rz(pi/2) q[3];
while (!c[0]) {
  x q[18];
  x q[54];
  cx q[67], q[3];
  h q[75];
  rz(pi/2) q[83];
  rz(pi/2) q[62];
  h q[82];
  h q[87];
  c[1] = measure q[67];
  if (c[1]) {
    h q[1];
    x q[46];
  }
  x q[66];
  t q[21];
  x q[5];
  s q[19];
  t q[2];
  h q[30];
  rz(pi/2) q[6];
  h q[6];
  c[2] = measure q[2];
  if (c[2]) {
    h q[23];
    h q[56];
  }
  rz(pi/2) q[60];
  s q[64];
  t q[25];
  cz q[86], q[77];
  rz(pi/2) q[61];
  x q[81];
  h q[16];
  x q[51];
  c[3] = measure q[43];
  if (c[3]) {
    cz q[72], q[69];
    h q[75];
  }
  rz(pi/2) q[99];
  cz q[55], q[54];
  rz(pi/2) q[77];
  s q[58];
  rz(pi/2) q[39];
  s q[7];
  rz(pi/2) q[28];
  h q[59];
  c[4] = measure q[85];
  if (c[4]) {
    cz q[13], q[86];
    s q[54];
  }
  h q[5];
  h q[2];
  x q[20];
  reset q[0];
  h q[0];
  c[0] = measure q[0];
}

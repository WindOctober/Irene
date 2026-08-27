OPENQASM 3.0;
include "stdgates.inc";
bit[10] c;
qubit[100] q;
t q[93];
rz(pi/2) q[28];
rz(pi/2) q[58];
cz q[72], q[2];
rz(pi/2) q[79];
while (!c[0]) {
  rz(pi/2) q[80];
  s q[18];
  rz(pi/2) q[10];
  cz q[31], q[56];
  c[1] = measure q[72];
  if (c[1]) {
    t q[74];
    h q[31];
  }
  h q[65];
  cz q[32], q[7];
  cz q[58], q[17];
  cx q[80], q[86];
  c[2] = measure q[81];
  if (c[2]) {
    t q[83];
    s q[3];
  }
  rz(pi/2) q[73];
  s q[80];
  cz q[25], q[37];
  x q[23];
  c[3] = measure q[55];
  if (c[3]) {
    s q[51];
    rz(pi/2) q[30];
  }
  h q[21];
  cz q[52], q[4];
  s q[61];
  h q[96];
  c[4] = measure q[81];
  if (c[4]) {
    rz(pi/2) q[8];
    cx q[79], q[56];
  }
  t q[96];
  cz q[35], q[92];
  x q[52];
  rz(pi/2) q[75];
  c[5] = measure q[1];
  if (c[5]) {
    rz(pi/2) q[69];
    rz(pi/2) q[61];
  }
  h q[68];
  h q[67];
  s q[9];
  rz(pi/2) q[58];
  c[6] = measure q[29];
  if (c[6]) {
    t q[79];
    s q[51];
  }
  s q[33];
  rz(pi/2) q[59];
  h q[3];
  cz q[24], q[36];
  c[7] = measure q[38];
  if (c[7]) {
    x q[73];
    rz(pi/2) q[52];
  }
  rz(pi/2) q[3];
  h q[25];
  s q[73];
  cz q[14], q[13];
  c[8] = measure q[98];
  if (c[8]) {
    h q[63];
    h q[86];
  }
  cz q[30], q[79];
  x q[39];
  x q[68];
  x q[9];
  c[9] = measure q[27];
  if (c[9]) {
    s q[86];
    t q[74];
  }
  reset q[0];
  h q[0];
  c[0] = measure q[0];
}

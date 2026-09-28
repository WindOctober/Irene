OPENQASM 3.0;
include "stdgates.inc";
bit[10] c;
qubit[100] q;
cx q[42], q[98];
x q[53];
h q[24];
cz q[44], q[70];
s q[20];
cx q[54], q[8];
cx q[40], q[6];
s q[49];
s q[7];
cx q[86], q[94];
while (!c[0]) {
  x q[51];
  s q[8];
  rz(pi/2) q[98];
  h q[75];
  cx q[79], q[25];
  t q[99];
  t q[58];
  t q[79];
  c[1] = measure q[56];
  if (c[1]) {
    x q[28];
    x q[39];
  }
  cz q[36], q[32];
  rz(pi/2) q[59];
  t q[18];
  x q[86];
  s q[86];
  s q[93];
  rz(pi/2) q[35];
  x q[39];
  c[2] = measure q[69];
  if (c[2]) {
    rz(pi/2) q[39];
    h q[3];
  }
  rz(pi/2) q[15];
  cz q[43], q[78];
  s q[38];
  cx q[9], q[88];
  rz(pi/2) q[57];
  h q[60];
  s q[96];
  rz(pi/2) q[14];
  c[3] = measure q[13];
  if (c[3]) {
    rz(pi/2) q[17];
    cx q[80], q[12];
  }
  x q[12];
  cz q[49], q[46];
  h q[3];
  t q[81];
  cx q[91], q[29];
  cz q[60], q[72];
  s q[91];
  h q[99];
  c[4] = measure q[58];
  if (c[4]) {
    s q[67];
    rz(pi/2) q[74];
  }
  h q[64];
  t q[28];
  x q[35];
  t q[79];
  t q[64];
  s q[80];
  cz q[2], q[99];
  s q[99];
  c[5] = measure q[66];
  if (c[5]) {
    x q[89];
    s q[23];
  }
  cz q[99], q[83];
  s q[64];
  x q[32];
  cz q[17], q[40];
  cz q[31], q[47];
  rz(pi/2) q[93];
  cx q[66], q[31];
  x q[39];
  c[6] = measure q[73];
  if (c[6]) {
    rz(pi/2) q[42];
    cz q[66], q[23];
  }
  x q[9];
  t q[28];
  t q[16];
  t q[59];
  s q[77];
  cx q[45], q[30];
  rz(pi/2) q[61];
  t q[84];
  c[7] = measure q[55];
  if (c[7]) {
    t q[91];
    cz q[36], q[28];
  }
  x q[58];
  t q[67];
  rz(pi/2) q[32];
  rz(pi/2) q[34];
  rz(pi/2) q[17];
  x q[31];
  x q[59];
  rz(pi/2) q[3];
  c[8] = measure q[82];
  if (c[8]) {
    s q[55];
    cz q[60], q[58];
  }
  x q[82];
  s q[70];
  h q[42];
  cz q[23], q[30];
  rz(pi/2) q[77];
  s q[49];
  cx q[21], q[7];
  cx q[5], q[41];
  c[9] = measure q[15];
  if (c[9]) {
    cz q[54], q[69];
    cx q[79], q[41];
  }
  reset q[0];
  h q[0];
  c[0] = measure q[0];
}

OPENQASM 3.0;
include "stdgates.inc";
bit[20] c;
qubit[100] q;
cx q[30], q[37];
h q[56];
cz q[2], q[69];
rz(pi/2) q[10];
cz q[53], q[85];
x q[77];
cz q[75], q[65];
cx q[23], q[24];
x q[95];
s q[5];
while (!c[0]) {
  cx q[61], q[13];
  s q[40];
  t q[61];
  s q[18];
  c[1] = measure q[8];
  if (c[1]) {
    t q[35];
    rz(pi/2) q[37];
  }
  h q[45];
  s q[4];
  x q[58];
  h q[77];
  c[2] = measure q[78];
  if (c[2]) {
    cz q[41], q[3];
    s q[39];
  }
  cx q[45], q[60];
  x q[33];
  rz(pi/2) q[6];
  cx q[61], q[8];
  c[3] = measure q[82];
  if (c[3]) {
    x q[36];
    cx q[5], q[52];
  }
  x q[61];
  t q[23];
  x q[15];
  cz q[22], q[93];
  c[4] = measure q[51];
  if (c[4]) {
    s q[42];
    x q[73];
  }
  h q[55];
  cx q[99], q[15];
  x q[79];
  cz q[58], q[14];
  c[5] = measure q[98];
  if (c[5]) {
    rz(pi/2) q[75];
    rz(pi/2) q[9];
  }
  t q[76];
  h q[25];
  s q[57];
  cx q[72], q[28];
  c[6] = measure q[77];
  if (c[6]) {
    x q[73];
    h q[93];
  }
  h q[89];
  cz q[91], q[83];
  cz q[45], q[21];
  h q[71];
  c[7] = measure q[96];
  if (c[7]) {
    x q[54];
    x q[27];
  }
  cx q[85], q[82];
  x q[56];
  t q[44];
  h q[27];
  c[8] = measure q[52];
  if (c[8]) {
    cx q[10], q[30];
    cz q[41], q[2];
  }
  rz(pi/2) q[18];
  t q[85];
  x q[37];
  t q[13];
  c[9] = measure q[80];
  if (c[9]) {
    cx q[84], q[77];
    x q[68];
  }
  h q[77];
  x q[73];
  cx q[7], q[58];
  rz(pi/2) q[62];
  c[10] = measure q[39];
  if (c[10]) {
    rz(pi/2) q[37];
    rz(pi/2) q[89];
  }
  cz q[95], q[14];
  x q[37];
  x q[64];
  cx q[28], q[4];
  c[11] = measure q[21];
  if (c[11]) {
    h q[26];
    h q[63];
  }
  s q[47];
  rz(pi/2) q[62];
  cx q[52], q[84];
  x q[69];
  c[12] = measure q[13];
  if (c[12]) {
    cz q[99], q[91];
    s q[47];
  }
  h q[41];
  cx q[41], q[88];
  t q[50];
  t q[33];
  c[13] = measure q[25];
  if (c[13]) {
    t q[3];
    cz q[72], q[27];
  }
  cz q[72], q[51];
  cx q[87], q[14];
  x q[57];
  cz q[24], q[79];
  c[14] = measure q[31];
  if (c[14]) {
    cx q[62], q[26];
    cx q[35], q[79];
  }
  s q[63];
  cx q[30], q[60];
  x q[53];
  x q[67];
  c[15] = measure q[71];
  if (c[15]) {
    cx q[36], q[81];
    t q[33];
  }
  s q[87];
  cx q[21], q[56];
  cx q[64], q[26];
  t q[34];
  c[16] = measure q[57];
  if (c[16]) {
    t q[67];
    cz q[46], q[96];
  }
  t q[77];
  cz q[31], q[2];
  x q[57];
  x q[74];
  c[17] = measure q[73];
  if (c[17]) {
    s q[41];
    h q[28];
  }
  rz(pi/2) q[30];
  rz(pi/2) q[53];
  h q[27];
  rz(pi/2) q[9];
  c[18] = measure q[38];
  if (c[18]) {
    t q[7];
    h q[31];
  }
  rz(pi/2) q[83];
  rz(pi/2) q[71];
  h q[34];
  x q[40];
  c[19] = measure q[64];
  if (c[19]) {
    rz(pi/2) q[34];
    cx q[35], q[63];
  }
  reset q[0];
  h q[0];
  c[0] = measure q[0];
}

OPENQASM 3.0;
include "stdgates.inc";
bit[20] c;
qubit[100] q;
rz(pi/2) q[41];
s q[34];
cx q[49], q[85];
t q[85];
x q[88];
rz(pi/2) q[49];
s q[37];
rz(pi/2) q[83];
cx q[71], q[5];
h q[70];
rz(pi/2) q[64];
cx q[96], q[67];
t q[93];
t q[41];
t q[64];
x q[13];
rz(pi/2) q[83];
cz q[99], q[30];
h q[69];
cz q[41], q[36];
while (!c[0]) {
  x q[21];
  h q[64];
  h q[51];
  rz(pi/2) q[88];
  h q[82];
  cx q[58], q[3];
  t q[13];
  t q[58];
  c[1] = measure q[91];
  if (c[1]) {
    cz q[3], q[54];
    s q[70];
  }
  s q[89];
  rz(pi/2) q[22];
  x q[44];
  cz q[36], q[64];
  x q[93];
  cz q[91], q[65];
  x q[54];
  rz(pi/2) q[67];
  c[2] = measure q[53];
  if (c[2]) {
    t q[57];
    cx q[41], q[15];
  }
  rz(pi/2) q[1];
  t q[59];
  x q[80];
  cz q[26], q[64];
  rz(pi/2) q[25];
  cx q[32], q[29];
  cx q[73], q[78];
  rz(pi/2) q[75];
  c[3] = measure q[69];
  if (c[3]) {
    x q[54];
    cz q[85], q[28];
  }
  x q[50];
  rz(pi/2) q[6];
  t q[34];
  h q[58];
  t q[37];
  cx q[80], q[64];
  cz q[23], q[53];
  h q[56];
  c[4] = measure q[48];
  if (c[4]) {
    h q[31];
    s q[33];
  }
  x q[93];
  x q[59];
  h q[61];
  cx q[78], q[60];
  rz(pi/2) q[93];
  t q[10];
  cx q[81], q[8];
  rz(pi/2) q[43];
  c[5] = measure q[88];
  if (c[5]) {
    cx q[5], q[81];
    s q[43];
  }
  t q[75];
  t q[6];
  s q[70];
  h q[50];
  t q[79];
  h q[41];
  cz q[13], q[44];
  s q[46];
  c[6] = measure q[78];
  if (c[6]) {
    t q[40];
    s q[28];
  }
  t q[88];
  cx q[1], q[11];
  rz(pi/2) q[27];
  x q[15];
  rz(pi/2) q[98];
  x q[71];
  x q[29];
  rz(pi/2) q[63];
  c[7] = measure q[38];
  if (c[7]) {
    cz q[38], q[44];
    t q[41];
  }
  cx q[92], q[42];
  h q[14];
  cz q[96], q[45];
  cz q[3], q[90];
  s q[9];
  h q[28];
  h q[33];
  rz(pi/2) q[68];
  c[8] = measure q[17];
  if (c[8]) {
    s q[8];
    rz(pi/2) q[90];
  }
  cx q[36], q[81];
  h q[60];
  h q[53];
  rz(pi/2) q[81];
  h q[98];
  cz q[33], q[63];
  cz q[28], q[53];
  h q[62];
  c[9] = measure q[9];
  if (c[9]) {
    cz q[14], q[27];
    h q[12];
  }
  s q[29];
  x q[42];
  t q[74];
  rz(pi/2) q[95];
  t q[47];
  x q[72];
  x q[33];
  s q[29];
  c[10] = measure q[70];
  if (c[10]) {
    rz(pi/2) q[20];
    t q[98];
  }
  x q[76];
  x q[30];
  rz(pi/2) q[91];
  t q[68];
  s q[23];
  s q[71];
  cx q[12], q[25];
  cx q[47], q[75];
  c[11] = measure q[81];
  if (c[11]) {
    rz(pi/2) q[44];
    cz q[29], q[13];
  }
  t q[71];
  t q[30];
  x q[96];
  rz(pi/2) q[67];
  cx q[8], q[67];
  cx q[71], q[56];
  x q[61];
  h q[46];
  c[12] = measure q[6];
  if (c[12]) {
    h q[21];
    x q[5];
  }
  s q[4];
  rz(pi/2) q[40];
  x q[63];
  h q[10];
  s q[83];
  rz(pi/2) q[15];
  t q[33];
  cz q[53], q[32];
  c[13] = measure q[35];
  if (c[13]) {
    cx q[52], q[62];
    cz q[19], q[33];
  }
  rz(pi/2) q[99];
  h q[3];
  h q[31];
  x q[35];
  cz q[88], q[63];
  cz q[9], q[67];
  rz(pi/2) q[34];
  cz q[96], q[78];
  c[14] = measure q[69];
  if (c[14]) {
    rz(pi/2) q[59];
    h q[28];
  }
  cz q[51], q[98];
  x q[1];
  x q[12];
  rz(pi/2) q[95];
  x q[69];
  s q[26];
  t q[39];
  cx q[9], q[8];
  c[15] = measure q[97];
  if (c[15]) {
    t q[65];
    h q[59];
  }
  rz(pi/2) q[88];
  cx q[48], q[56];
  t q[34];
  rz(pi/2) q[47];
  h q[61];
  t q[84];
  s q[75];
  h q[72];
  c[16] = measure q[48];
  if (c[16]) {
    s q[1];
    h q[18];
  }
  cz q[69], q[57];
  h q[60];
  s q[8];
  t q[2];
  x q[18];
  h q[67];
  x q[15];
  rz(pi/2) q[21];
  c[17] = measure q[42];
  if (c[17]) {
    cz q[74], q[32];
    h q[92];
  }
  x q[65];
  h q[37];
  t q[5];
  s q[16];
  h q[93];
  h q[89];
  x q[98];
  s q[83];
  c[18] = measure q[93];
  if (c[18]) {
    t q[37];
    t q[63];
  }
  rz(pi/2) q[51];
  rz(pi/2) q[90];
  cz q[25], q[86];
  t q[20];
  cz q[97], q[21];
  rz(pi/2) q[34];
  t q[29];
  h q[14];
  c[19] = measure q[12];
  if (c[19]) {
    cz q[76], q[6];
    cz q[63], q[8];
  }
  reset q[0];
  h q[0];
  c[0] = measure q[0];
}

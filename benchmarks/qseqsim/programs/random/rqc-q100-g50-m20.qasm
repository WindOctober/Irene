OPENQASM 3.0;
include "stdgates.inc";
bit[20] c;
qubit[100] q;
x q[85];
h q[47];
x q[94];
rz(pi/2) q[16];
rz(pi/2) q[60];
while (!c[0]) {
  cz q[4], q[41];
  x q[90];
  c[1] = measure q[47];
  if (c[1]) {
    cz q[55], q[65];
    cx q[65], q[60];
  }
  cz q[44], q[5];
  x q[27];
  c[2] = measure q[76];
  if (c[2]) {
    s q[90];
    s q[96];
  }
  t q[55];
  t q[89];
  c[3] = measure q[19];
  if (c[3]) {
    s q[57];
    rz(pi/2) q[4];
  }
  x q[29];
  rz(pi/2) q[75];
  c[4] = measure q[64];
  if (c[4]) {
    t q[75];
    cx q[64], q[50];
  }
  cx q[23], q[33];
  x q[75];
  c[5] = measure q[24];
  if (c[5]) {
    rz(pi/2) q[3];
    x q[54];
  }
  t q[47];
  cz q[86], q[22];
  c[6] = measure q[27];
  if (c[6]) {
    rz(pi/2) q[48];
    rz(pi/2) q[93];
  }
  cz q[12], q[38];
  t q[31];
  c[7] = measure q[5];
  if (c[7]) {
    cz q[77], q[58];
    x q[36];
  }
  s q[19];
  rz(pi/2) q[40];
  c[8] = measure q[2];
  if (c[8]) {
    cz q[60], q[92];
    cx q[56], q[78];
  }
  cz q[48], q[80];
  cz q[54], q[9];
  c[9] = measure q[4];
  if (c[9]) {
    rz(pi/2) q[21];
    x q[42];
  }
  cz q[62], q[52];
  rz(pi/2) q[4];
  c[10] = measure q[51];
  if (c[10]) {
    rz(pi/2) q[87];
    x q[71];
  }
  x q[17];
  s q[42];
  c[11] = measure q[55];
  if (c[11]) {
    cx q[78], q[8];
    cx q[19], q[5];
  }
  cx q[54], q[82];
  x q[8];
  c[12] = measure q[49];
  if (c[12]) {
    cx q[61], q[96];
    h q[95];
  }
  cz q[22], q[38];
  h q[20];
  c[13] = measure q[63];
  if (c[13]) {
    cz q[86], q[78];
    t q[75];
  }
  h q[82];
  cz q[17], q[44];
  c[14] = measure q[56];
  if (c[14]) {
    rz(pi/2) q[7];
    x q[56];
  }
  s q[65];
  t q[96];
  c[15] = measure q[90];
  if (c[15]) {
    x q[95];
    t q[42];
  }
  cz q[88], q[17];
  cx q[25], q[64];
  c[16] = measure q[80];
  if (c[16]) {
    t q[45];
    rz(pi/2) q[99];
  }
  s q[45];
  cx q[1], q[63];
  c[17] = measure q[98];
  if (c[17]) {
    rz(pi/2) q[67];
    rz(pi/2) q[90];
  }
  cz q[34], q[1];
  cx q[47], q[48];
  c[18] = measure q[41];
  if (c[18]) {
    h q[15];
    h q[59];
  }
  t q[42];
  rz(pi/2) q[22];
  c[19] = measure q[80];
  if (c[19]) {
    t q[87];
    h q[79];
  }
  reset q[0];
  h q[0];
  c[0] = measure q[0];
}

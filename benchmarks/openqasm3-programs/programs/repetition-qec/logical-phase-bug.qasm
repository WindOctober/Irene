OPENQASM 3.0;
include "stdgates.inc";

qubit[3] data;
qubit[2] ancilla;
bit[2] syndrome;

def measure_syndrome(qubit[3] d, qubit[2] a) -> bit[2] {
  bit[2] result;
  reset a;
  cx d[0], a[0];
  cx d[1], a[0];
  cx d[1], a[1];
  cx d[2], a[1];
  result = measure a;
  return result;
}

reset data[1];
reset data[2];
cx data[0], data[1];
cx data[0], data[2];

x data[0];
syndrome = measure_syndrome(data, ancilla);
if (int[2](syndrome) == 1) x data[0];
if (int[2](syndrome) == 2) x data[2];
if (int[2](syndrome) == 3) x data[1];
z data[0];

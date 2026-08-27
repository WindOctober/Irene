OPENQASM 3.0;
include "stdgates.inc";

def segment(qubit[2] ancilla, qubit psi) -> bit[2] {
  bit[2] result;
  reset ancilla;
  h ancilla;
  ccx ancilla[0], ancilla[1], psi;
  s psi;
  ccx ancilla[0], ancilla[1], psi;
  z psi;
  h ancilla;
  result = measure ancilla;
  return result;
}

qubit[1] input_qubit;
qubit[2] ancilla;
bit[2] flags = "11";

while (int[2](flags) != 0) {
  flags = segment(ancilla, input_qubit[0]);
}
rz(pi + arccos(3 / 5)) input_qubit[0];

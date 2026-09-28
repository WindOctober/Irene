OPENQASM 3.0;
include "stdgates.inc";

const uint[32] hops = 10;

qubit input_qubit;
qubit[2 * hops] q;

def teleport_and_correct(qubit source, qubit[2] bell) {
  bit phase_measurement;
  bit bit_measurement;

  reset bell;
  h bell[0];
  cx bell[0], bell[1];
  cx source, bell[0];
  h source;
  phase_measurement = measure source;
  bit_measurement = measure bell[0];
  if (phase_measurement == true) z bell[1];
  if (bit_measurement == true) x bell[1];
}

teleport_and_correct(input_qubit, q[0:1]);
for uint i in [1:hops - 1] {
  teleport_and_correct(q[2 * i - 1], q[2 * i:2 * i + 1]);
}

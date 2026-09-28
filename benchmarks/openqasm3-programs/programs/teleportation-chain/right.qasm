OPENQASM 3.0;
include "stdgates.inc";

const uint[32] hops = 10;

qubit input_qubit;
qubit[2 * hops] q;
bit phase_frame = false;
bit bit_frame = false;

def teleport_raw(qubit source, qubit[2] bell) -> bit[2] {
  bit[2] result;

  reset bell;
  h bell[0];
  cx bell[0], bell[1];
  cx source, bell[0];
  h source;
  result[0] = measure source;
  result[1] = measure bell[0];
  return result;
}

bit[2] measured;
measured = teleport_raw(input_qubit, q[0:1]);
phase_frame ^= measured[0];
bit_frame ^= measured[1];
for uint i in [1:hops - 1] {
  measured = teleport_raw(q[2 * i - 1], q[2 * i:2 * i + 1]);
  phase_frame ^= measured[0];
  bit_frame ^= measured[1];
}

// Materialize the accumulated frame once, rather than after every hop.
if (phase_frame == true) z q[19];
if (bit_frame == true) x q[19];

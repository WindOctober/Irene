OPENQASM 3.0;
include "stdgates.inc";

qubit[3] data;
qubit[3] magic;
bit[3] measured_magic;
bit logical_measurement;

reset data[1];
reset data[2];
cx data[0], data[1];
cx data[0], data[2];

// Prepare the encoded magic state (|000> + exp(i*pi/4)|111>)/sqrt(2).
reset magic;
h magic[0];
t magic[0];
cx magic[0], magic[1];
cx magic[0], magic[2];

// Teleport T into the encoded data and decode the logical measurement by vote.
cx data[0], magic[0];
cx data[1], magic[1];
cx data[2], magic[2];
measured_magic = measure magic;
logical_measurement =
  (measured_magic[0] & measured_magic[1]) |
  (measured_magic[0] & measured_magic[2]) |
  (measured_magic[1] & measured_magic[2]);
if (logical_measurement == true) s data[0];

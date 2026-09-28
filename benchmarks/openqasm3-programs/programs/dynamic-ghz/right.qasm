OPENQASM 3.0;
include "stdgates.inc";

qubit[8] data;
qubit[7] ancilla;
bit[7] syndrome;

reset data;
reset ancilla;
h data;

// Measure all adjacent ZZ parities using two entangling layers.
cx data[0], ancilla[0];
cx data[1], ancilla[1];
cx data[2], ancilla[2];
cx data[3], ancilla[3];
cx data[4], ancilla[4];
cx data[5], ancilla[5];
cx data[6], ancilla[6];
cx data[1], ancilla[0];
cx data[2], ancilla[1];
cx data[3], ancilla[2];
cx data[4], ancilla[3];
cx data[5], ancilla[4];
cx data[6], ancilla[5];
cx data[7], ancilla[6];
syndrome = measure ancilla;

// Prefix parity maps the measured cat-state representative to GHZ.
if (syndrome[0] == true) x data[1];
if ((syndrome[0] ^ syndrome[1]) == true) x data[2];
if ((syndrome[0] ^ syndrome[1] ^ syndrome[2]) == true) x data[3];
if ((syndrome[0] ^ syndrome[1] ^ syndrome[2] ^ syndrome[3]) == true) x data[4];
if ((syndrome[0] ^ syndrome[1] ^ syndrome[2] ^ syndrome[3] ^ syndrome[4]) == true) x data[5];
if ((syndrome[0] ^ syndrome[1] ^ syndrome[2] ^ syndrome[3] ^ syndrome[4] ^ syndrome[5]) == true) x data[6];
if ((syndrome[0] ^ syndrome[1] ^ syndrome[2] ^ syndrome[3] ^ syndrome[4] ^ syndrome[5] ^ syndrome[6]) == true) x data[7];

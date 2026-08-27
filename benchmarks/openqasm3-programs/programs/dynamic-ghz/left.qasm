OPENQASM 3.0;
include "stdgates.inc";

qubit[8] data;
qubit[7] ancilla;

reset data;
reset ancilla;
h data[0];
cx data[0], data[1];
cx data[1], data[2];
cx data[2], data[3];
cx data[3], data[4];
cx data[4], data[5];
cx data[5], data[6];
cx data[6], data[7];

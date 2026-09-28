OPENQASM 3.0;
include "stdgates.inc";

qubit[3] data;

reset data[1];
reset data[2];
cx data[0], data[1];
cx data[0], data[2];

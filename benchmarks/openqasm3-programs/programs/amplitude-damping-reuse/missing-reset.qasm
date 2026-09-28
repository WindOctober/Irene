OPENQASM 3.0;
include "stdgates.inc";

qubit system;
qubit environment;
bit first_jump;
bit second_jump;

reset environment;
ctrl @ ry(pi / 3) system, environment;
cx environment, system;
first_jump = measure environment;

// Reusing a measured |1> environment without reset can re-excite the system.
ctrl @ ry(pi / 3) system, environment;
cx environment, system;
second_jump = measure environment;

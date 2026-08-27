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

// The measured environment is reset and reused for the second channel step.
reset environment;
ctrl @ ry(pi / 3) system, environment;
cx environment, system;
second_jump = measure environment;

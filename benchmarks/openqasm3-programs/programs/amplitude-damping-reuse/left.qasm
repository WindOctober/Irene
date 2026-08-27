OPENQASM 3.0;
include "stdgates.inc";

qubit system;
qubit[2] environment;

reset environment;

// Two amplitude-damping steps with gamma = sin(pi/6)^2 = 1/4.
ctrl @ ry(pi / 3) system, environment[0];
cx environment[0], system;
ctrl @ ry(pi / 3) system, environment[1];
cx environment[1], system;

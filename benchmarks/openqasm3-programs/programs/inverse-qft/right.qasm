OPENQASM 3.0;
include "stdgates.inc";

qubit[4] q;
bit c0;
bit c1;
bit c2;
bit c3;

h q[0];
c0 = measure q[0];
if (c0 == true) rz(pi / 2) q[1];
h q[1];
c1 = measure q[1];
if (c0 == true) rz(pi / 4) q[2];
if (c1 == true) rz(pi / 2) q[2];
h q[2];
c2 = measure q[2];
if (c0 == true) rz(pi / 8) q[3];
if (c1 == true) rz(pi / 4) q[3];
if (c2 == true) rz(pi / 2) q[3];
h q[3];
c3 = measure q[3];

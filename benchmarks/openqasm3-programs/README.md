# OpenQASM 3 program pairs

These 26 pairs are fixed implementations of concrete quantum algorithms,
protocols, and compiler transformations. They are derived from the official
OpenQASM examples and published work on dynamic circuits, MBQC, long-range
entanglement, state preparation, fault-tolerant gate injection, and open-system
simulation. Each task makes its compared input and output interface explicit.

The inverse-QFT pair factors value-enumerating feedback into independent
bit-controlled rotations. The teleportation pairs check the identity channel,
a measured-qubit reuse transformation, and a classical Pauli-frame
optimization for Z-observed output. The IPE pair fuses feedback phase and
Hadamard gates inside the original loop. The RUS pair checks the almost-sure
loop against its identity-channel specification. The QEC pair checks recovery
from a single injected bit-flip for an arbitrary logical input.

Five non-equivalent variants model deeper bugs in adaptive programs: a late
inverse-QFT feedback angle, a missing teleportation phase correction,
overwritten measurement history during qubit reuse, a logical QEC phase error,
and an incorrect RUS compensation angle.

The additional fixed instances cover:

- logical T gate teleportation on a three-qubit repetition code;
- physical `Ry(pi/4)` magic-state injection;
- a ten-hop teleportation chain with one final Pauli-frame correction;
- a nearest-neighbor remote CNOT implemented by gate teleportation;
- a two-step adaptive MBQC rotation pattern;
- constant-depth dynamic preparation of GHZ-8;
- two rounds of amplitude damping with environment-qubit reuse.

Their equivalent transformations have concrete resource goals. Pauli-frame
aggregation replaces twenty conditional quantum corrections with two final
corrections. Remote CNOT replaces a four-SWAP routing network (thirteen CNOTs
after decomposition) with three CNOTs, two measurements, and feed-forward.
Dynamic GHZ reduces entangling depth from seven dependent CNOTs to two parity
measurement layers. Environment reuse reduces two damping ancillas to one.
Magic-state and MBQC cases model fault-tolerant or measurement-based lowering,
where resource states may be prepared off the online data path.

Each new family also has a non-equivalent partner whose defect occurs in a
later measurement branch, parity computation, adaptive angle, correction, or
reuse step. These are intended to require phase-sensitive or branch-sensitive
witnesses rather than only computational-basis testing.

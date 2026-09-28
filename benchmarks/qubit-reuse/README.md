# Qubit reuse

These ten closed OpenQASM 2 program pairs compare seeded Clifford+T circuits
with the output of Qiskit's `qubit_reuse` compilation pass. Each left program
initializes all qubits to zero and measures every output. Each right program
uses fewer physical qubits and contains measurement followed by reset and
reuse. The observed classical output bits are paired explicitly.

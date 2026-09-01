# QUMUG hard mutants

This collection contains one first-order QUMUG mutant for each of the 30
MQT Bench circuits used in the QUMUG evaluation. For every source circuit, the
selected mutant is the GA-generated first-order mutant with the lowest
non-zero CTS detection rate in the published results, with run and individual
identifiers recorded in the manifest.

The original programs contain only unitary gates followed by final
measurements. The benchmark compares their quantum circuit-under-test before
measurement, so every declared qubit is both an arbitrary input and an
observable quantum output. Final measurements and barriers are removed from
both sides; the selected mutation is the only semantic difference.

QUMUG classifies these mutants as non-equivalent because at least one test in
its comprehensive test suite distinguishes them. The imported unitary pairs
were also checked directly and none are equivalent up to global phase. The
source artifact is available at https://zenodo.org/records/21718539.

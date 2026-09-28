#!/usr/bin/env python3
import argparse
import json
import re
import sys

import numpy as np


ENDPOINT = re.compile(r"^(quantum|classical):([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]$")


class Unsupported(Exception):
    pass


def emit(payload):
    print("RESULT_JSON=" + json.dumps(payload, sort_keys=True))


def endpoint(text):
    match = ENDPOINT.match(text)
    if not match:
        raise Unsupported(f"invalid endpoint: {text}")
    return match.group(1), match.group(2), int(match.group(3))


def pair_sides(text):
    left, right = text.split("=", 1)
    return endpoint(left), endpoint(right)


def reshape_gate(matrix):
    if matrix.shape == (1, 1):
        return matrix[0, 0]
    pieces = np.split(matrix, 2, 1 if matrix.shape[0] == matrix.shape[1] else 0)
    return np.array([reshape_gate(pieces[0]), reshape_gate(pieces[1])])


def endpoint_key(ep, role):
    kind, register, index = ep
    if kind == "classical":
        if role == "input":
            raise Unsupported("VeriQC does not model classical input registers")
        return f"{register}_{index}"
    return ("x" if role == "input" else "y") + str(index)


def rename_network(tn, indices, mapping):
    for tensor in tn.tensors:
        for index in tensor.index_set:
            if index.key in mapping:
                index.key = mapping[index.key]
    return [mapping.get(name, name) for name in indices]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("case_file")
    parser.add_argument("--repo", required=True)
    args = parser.parse_args()
    with open(args.case_file, encoding="utf-8") as handle:
        case = json.load(handle)

    if case["equivalence"] == "partial":
        emit({"results": [{"variant": "tdd", "status": "unsupported", "verdict": None,
                            "message": "VeriQC has no reset/discard partial-equivalence semantics"}]})
        return

    sys.path.insert(0, args.repo)
    try:
        from qiskit import QuantumCircuit
        from qiskit.circuit import Clbit, Qubit

        for cls in (Qubit, Clbit):
            cls.index = property(lambda value: value._index)
            cls.register = property(lambda value: value._register)

        import TDD2.TDD_Q as tdd_q
        from TDD2.TDD import Ini_TDD

        tdd_q.reshape = reshape_gate
        left_circuit = QuantumCircuit.from_qasm_file(case["left_abs"])
        right_circuit = QuantumCircuit.from_qasm_file(case["right_abs"])
        if len(left_circuit.qregs) != 1 or len(right_circuit.qregs) != 1:
            raise Unsupported("VeriQC's converter assumes one quantum register")

        left_tn, left_indices = tdd_q.cir_2_tn(left_circuit)
        right_tn, right_indices = tdd_q.cir_2_tn(right_circuit)
        left_map = {}
        right_map = {}
        for position, raw_pair in enumerate(case["input_pairs"]):
            left, right = pair_sides(raw_pair)
            left_map[endpoint_key(left, "input")] = f"__input_{position}"
            right_map[endpoint_key(right, "input")] = f"__input_{position}"
        for position, raw_pair in enumerate(case["output_pairs"]):
            left, right = pair_sides(raw_pair)
            left_map[endpoint_key(left, "output")] = f"__output_{position}"
            right_map[endpoint_key(right, "output")] = f"__output_{position}"

        left_indices = rename_network(left_tn, left_indices, left_map)
        right_indices = rename_network(right_tn, right_indices, right_map)
        order = []
        for name in left_indices + right_indices:
            if name not in order:
                order.append(name)
        Ini_TDD(order)
        left_tdd = left_tn.cont(optimizer="tree_decomposition")[0]
        right_tdd = right_tn.cont(optimizer="tree_decomposition")[0]
        equivalent = left_tdd == right_tdd
        emit(
            {
                "results": [
                    {
                        "variant": "tdd",
                        "status": "completed",
                        "verdict": "eq" if equivalent else "neq",
                        "native_result": str(equivalent),
                        "left_nodes": left_tdd.node_number(),
                        "right_nodes": right_tdd.node_number(),
                    }
                ]
            }
        )
    except Unsupported as exc:
        emit({"results": [{"variant": "tdd", "status": "unsupported", "verdict": None, "message": str(exc)}]})
    except Exception as exc:
        text = f"{type(exc).__name__}: {exc}"
        markers = ("cannot apply operation: reset", "not defined in this scope", "unsupported")
        status = "unsupported" if any(marker in text.lower() for marker in markers) else "error"
        emit({"results": [{"variant": "tdd", "status": status, "verdict": None, "message": text}]})


if __name__ == "__main__":
    main()

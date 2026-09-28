#!/usr/bin/env python3
import argparse
import json
import re
import subprocess
from pathlib import Path


ENDPOINT = re.compile(r"^(quantum|classical):([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]$")
QREG = re.compile(r"\bqreg\s+([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*;")
MEASURE = re.compile(
    r"\bmeasure\s+([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*->\s*"
    r"([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*;"
)


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


def qasm_layout(path):
    text = Path(path).read_text(encoding="utf-8")
    offsets = {}
    width = 0
    for register, size in QREG.findall(text):
        offsets[register] = width
        width += int(size)
    measured = {}
    for qreg, qindex, creg, cindex in MEASURE.findall(text):
        if qreg not in offsets:
            raise Unsupported(f"unknown quantum register {qreg}")
        measured[(creg, int(cindex))] = offsets[qreg] + int(qindex)
    return offsets, measured


def quantum_index(ep, layout, role):
    kind, register, index = ep
    offsets, measured = layout
    if kind == "quantum":
        if register not in offsets:
            raise Unsupported(f"unknown quantum register {register}")
        return offsets[register] + index
    if role == "input":
        raise Unsupported("SQbricks does not accept classical input wires")
    try:
        return measured[(register, index)]
    except KeyError as exc:
        raise Unsupported(f"no measurement defines {register}[{index}]") from exc


def ocaml_list(values):
    return "[" + ";".join(str(value) for value in values) + "]"


def run(command, cwd):
    completed = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    print("COMMAND " + " ".join(str(part) for part in command))
    if completed.stdout:
        print("STDOUT " + completed.stdout.rstrip())
    if completed.stderr:
        print("STDERR " + completed.stderr.rstrip())
    if completed.returncode != 0:
        raise RuntimeError(f"command exited {completed.returncode}: {completed.stderr.strip()}")
    return completed.stdout.strip()


def classify(native):
    try:
        float(native)
        return "eq"
    except ValueError:
        pass
    if native == "NotEquivDiffMeasurements":
        return "unknown"
    if native.startswith("NotEquiv"):
        return "neq"
    return "unknown"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("case_file")
    parser.add_argument("--repo", required=True)
    parser.add_argument("--tmp", required=True)
    args = parser.parse_args()
    with open(args.case_file, encoding="utf-8") as handle:
        case = json.load(handle)

    repo = str(Path(args.repo).resolve())
    executable = str(Path(repo) / "_build/default/bin/main.exe")
    temp = Path(args.tmp)
    temp.mkdir(parents=True, exist_ok=True)
    left_u = str(temp / "left-unitary.qasm")
    right_u = str(temp / "right-unitary.qasm")
    try:
        left_layout = qasm_layout(case["left_abs"])
        right_layout = qasm_layout(case["right_abs"])
        left_inputs, right_inputs = [], []
        for raw_pair in case["input_pairs"]:
            left, right = pair_sides(raw_pair)
            left_inputs.append(quantum_index(left, left_layout, "input"))
            right_inputs.append(quantum_index(right, right_layout, "input"))
        left_outputs, right_outputs = [], []
        left_measured, right_measured = [], []
        for raw_pair in case["output_pairs"]:
            left, right = pair_sides(raw_pair)
            left_index = quantum_index(left, left_layout, "output")
            right_index = quantum_index(right, right_layout, "output")
            left_outputs.append(left_index)
            right_outputs.append(right_index)
            # A mixed quantum/classical pair is compared on its quantum carriers
            # before deferred measurement, as in SQbricks' upstream lifting run.
            if left[0] == "classical" and right[0] == "classical":
                left_measured.append(left_index)
                right_measured.append(right_index)

        run([executable, "-sql", "u", case["left_abs"], left_u], repo)
        run([executable, "-sql", "u", case["right_abs"], right_u], repo)
        common = [
            "s", left_u, right_u,
            ocaml_list(left_inputs), ocaml_list(right_inputs),
            ocaml_list(left_outputs), ocaml_list(right_outputs),
            ocaml_list(left_measured), ocaml_list(right_measured),
        ]
        results = []
        for algorithm in case.get("sqbricks_variants", ("seq", "par")):
            try:
                native = run([executable, "-sqv", algorithm] + common, repo)
                results.append({"variant": algorithm, "status": "completed",
                                "verdict": classify(native), "native_result": native})
            except Exception as exc:
                results.append({"variant": algorithm, "status": "error", "verdict": None,
                                "message": f"{type(exc).__name__}: {exc}"})
        emit({"results": results})
    except Unsupported as exc:
        emit({"results": [
            {"variant": "seq", "status": "unsupported", "verdict": None, "message": str(exc)},
            {"variant": "par", "status": "unsupported", "verdict": None, "message": str(exc)},
        ]})
    except Exception as exc:
        text = f"{type(exc).__name__}: {exc}"
        status = "unsupported" if "unsupported" in text.lower() else "error"
        emit({"results": [
            {"variant": "seq", "status": status, "verdict": None, "message": text},
            {"variant": "par", "status": status, "verdict": None, "message": text},
        ]})


if __name__ == "__main__":
    main()

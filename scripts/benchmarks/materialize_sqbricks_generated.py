#!/usr/bin/env python3
import argparse
import json
import os
import re
import resource
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SQBRICKS = ROOT / "tools" / "qbricks.github.io" / "Artifacts" / "SQbricks" / "SQbricks"
SQ_RUN = ROOT / "tools" / "envs" / "bin" / "sqbricks-run"
SQ_MAIN = SQBRICKS / "_build" / "default" / "bin" / "main.exe"
QISKIT = SQBRICKS / "envs" / "python" / "bin" / "python"
QISKIT_TRANSPILE = SQBRICKS / "scripts" / "qiskit-tr.py"
QBIRCKS = ROOT / "tools" / "envs" / "bin" / "qbircks-translate"
DEST = ROOT / "Irene" / "benchmarks" / "sqbricks" / "generated"
STATE = ROOT / "var" / "benchmarks" / "sqbricks-generated"
SUITES = ("qiskit-hybrid", "owm-vs-qiskit", "owm-vs-tele")
SOURCE_ALIASES = {
    "benchmarks/Feynman/qft_4.qasm": "benchmarks/Feynman/qft_4_feynman.qasm",
}
SOURCE_PROVENANCE = {
    "benchmarks/Feynman/qft_4_feynman.qasm": "benchmarks/Feynman/qft_4.qasm",
    "benchmarks/VeriQbench/dynamic/dqc_bitflip_code_corrected.qasm":
        "sqbricks-derived:VeriQbench/dynamic/dqc_bitflip_code.qasm",
    "benchmarks/VeriQbench/dynamic/dqc_phaseflip_code_corrected.qasm":
        "sqbricks-derived:VeriQbench/dynamic/dqc_phaseflip_code.qasm",
    "benchmarks/QASMBench/small/shor_n5/shor_n5_ancillas.qasm":
        "sqbricks-reset-to-ancilla:QASMBench/small/shor_n5/shor_n5.qasm",
}

QREG = re.compile(r"\bqreg\s+([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*;")
MEASURE = re.compile(
    r"\bmeasure\s+([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*->\s*"
    r"([A-Za-z_][A-Za-z0-9_]*)\[(\d+)\]\s*;"
)


def atomic_write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    os.replace(temporary, path)


def memory_limit(gib):
    def apply():
        limit = int(gib * 1024**3)
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    return apply


def run(command, timeout, memory_gib, stdout_path=None):
    completed = subprocess.run(
        [str(part) for part in command],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        preexec_fn=memory_limit(memory_gib),
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"command exited {completed.returncode}: {' '.join(str(x) for x in command)}\n"
            f"{completed.stderr.strip()}"
        )
    if stdout_path is not None:
        atomic_write(stdout_path, completed.stdout)
    return completed.stdout.strip()


def normalize(path):
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
    if text and not text.endswith("\n"):
        text += "\n"
    atomic_write(path, text)


def parse_int_list(text):
    text = text.strip()
    if not (text.startswith("[") and text.endswith("]")):
        raise ValueError(f"invalid SQbricks list: {text}")
    body = text[1:-1].strip()
    return [] if not body else [int(value) for value in body.split(";")]


def parse_interface(text):
    left, right = text.strip().split(",", 1)
    return parse_int_list(left), parse_int_list(right)


def qasm_layout(path):
    text = path.read_text(encoding="utf-8")
    quantum = []
    offsets = {}
    for register, raw_size in QREG.findall(text):
        offsets[register] = len(quantum)
        quantum.extend((register, index) for index in range(int(raw_size)))
    if not quantum:
        raise ValueError(f"no qreg declarations in {path}")
    measured = {}
    for qreg, qindex, creg, cindex in MEASURE.findall(text):
        flat = offsets[qreg] + int(qindex)
        measured[flat] = (creg, int(cindex))
    return quantum, measured


def input_endpoint(layout, index):
    quantum, _ = layout
    register, offset = quantum[index]
    return f"quantum:{register}[{offset}]"


def output_endpoint(layout, index):
    quantum, measured = layout
    if index in measured:
        register, offset = measured[index]
        return f"classical:{register}[{offset}]"
    register, offset = quantum[index]
    return f"quantum:{register}[{offset}]"


def compatible(path, timeout, memory_gib):
    try:
        run(
            [QBIRCKS, "openqasm2_to_qbircks", "-i", path, "-o", "/dev/null"],
            timeout,
            memory_gib,
        )
        return True
    except (RuntimeError, subprocess.TimeoutExpired):
        return False


def source_paths(suite):
    path_file = SQBRICKS / "scripts" / "paths" / f"paths_{suite}.txt"
    return [line.strip() for line in path_file.read_text(encoding="utf-8").splitlines() if line.strip()]


def case_sources(suite, source_rel):
    source = SOURCE_PROVENANCE.get(source_rel, source_rel)
    if suite == "qiskit-hybrid":
        return source, f"qiskit-transpile:{source}"
    if suite == "owm-vs-qiskit":
        return f"qasm-to-owm:{source}", f"qiskit-transpile:{source}"
    return f"qasm-to-owm:{source}", f"qasm-to-tele:{source}"


def materialize(item, timeout, memory_gib):
    suite, index, source_rel = item
    case_id = f"sqbricks-{suite}-{index:04d}"
    source = SQBRICKS / SOURCE_ALIASES.get(source_rel, source_rel)
    if not source.is_file():
        return {"id": case_id, "suite": suite, "source": source_rel, "status": "missing"}

    case_dir = DEST / "programs" / suite / f"{index:04d}"
    temp = STATE / "tmp" / case_id
    case_dir.mkdir(parents=True, exist_ok=True)
    temp.mkdir(parents=True, exist_ok=True)
    left = case_dir / "left.qasm"
    right = case_dir / "right.qasm"
    source_u = temp / "source-u.qasm"

    if suite == "qiskit-hybrid":
        atomic_write(left, source.read_text(encoding="utf-8"))
        run([QISKIT, QISKIT_TRANSPILE, source, right], timeout, memory_gib)
        equivalence = "hybrid"
    elif suite == "owm-vs-qiskit":
        run([SQ_RUN, SQ_MAIN, "-sql", "u", source, source_u], timeout, memory_gib)
        interface_left = run(
            [SQ_RUN, SQ_MAIN, "-qasm_to_owm", source_u, left, "false"], timeout, memory_gib
        )
        run([QISKIT, QISKIT_TRANSPILE, source, right], timeout, memory_gib)
        equivalence = "partial"
    else:
        run([SQ_RUN, SQ_MAIN, "-sql", "u", source, source_u], timeout, memory_gib)
        interface_left = run(
            [SQ_RUN, SQ_MAIN, "-qasm_to_owm", source_u, left, "false"], timeout, memory_gib
        )
        interface_right = run(
            [SQ_RUN, SQ_MAIN, "-qasm_to_tele", source_u, right, "false"], timeout, memory_gib
        )
        equivalence = "partial"

    source_left, source_right = case_sources(suite, source_rel)

    normalize(left)
    normalize(right)
    left_layout = qasm_layout(left)
    right_layout = qasm_layout(right)

    if suite == "qiskit-hybrid":
        if len(left_layout[0]) != len(right_layout[0]):
            raise ValueError(f"qiskit changed quantum width for {case_id}")
        left_inputs = right_inputs = list(range(len(left_layout[0])))
        left_outputs = right_outputs = list(range(len(left_layout[0])))
    elif suite == "owm-vs-qiskit":
        left_inputs, left_outputs = parse_interface(interface_left)
        right_inputs = list(range(len(right_layout[0])))
        right_outputs = list(range(len(right_layout[0])))
    else:
        left_inputs, left_outputs = parse_interface(interface_left)
        right_inputs, right_outputs = parse_interface(interface_right)

    if len(left_inputs) != len(right_inputs):
        raise ValueError(f"input width mismatch for {case_id}")
    if len(left_outputs) != len(right_outputs):
        raise ValueError(f"output width mismatch for {case_id}")

    input_pairs = [
        f"{input_endpoint(left_layout, left_index)}={input_endpoint(right_layout, right_index)}"
        for left_index, right_index in zip(left_inputs, right_inputs)
    ]
    output_pairs = [
        f"{output_endpoint(left_layout, left_index)}={output_endpoint(right_layout, right_index)}"
        for left_index, right_index in zip(left_outputs, right_outputs)
    ]
    qbircks_compatible = compatible(left, timeout, memory_gib) and compatible(
        right, timeout, memory_gib
    )

    return {
        "id": case_id,
        "suite": suite,
        "left": str(left.relative_to(DEST)),
        "right": str(right.relative_to(DEST)),
        "truth": "neq" if case_id in {"sqbricks-owm-vs-qiskit-0050", "sqbricks-owm-vs-qiskit-0051", "sqbricks-owm-vs-qiskit-0055"} else "eq",  # Audited errata, 2026-09-15.
        "equivalence": equivalence,
        "input_pairs": input_pairs,
        "output_pairs": output_pairs,
        "qbircks_compatible": qbircks_compatible,
        "source_left": source_left,
        "source_right": source_right,
        "source": source_rel,
        "status": "completed",
    }


def toml_string(value):
    return json.dumps(value, ensure_ascii=False)


def render_manifest(cases):
    lines = [
        "schema_version = 1",
        'program_format = "openqasm2"',
        "",
        "[source]",
        'id = "sqbricks"',
        'name = "SQbricks"',
        'repository = "https://github.com/Qbricks/qbricks.github.io"',
        'commit = "e00fc97f14fb9fcbc44bbfbc5e5ec3e483f87367"',
        "",
        "[normalization]",
        'encoding = "utf-8"',
        'line_endings = "lf"',
        "semantic_rewrite = false",
        "",
    ]
    for case in cases:
        lines.extend(
            [
                "[[case]]",
                f'id = {toml_string(case["id"])}',
                f'suite = {toml_string(case["suite"])}',
                f'left = {toml_string(case["left"])}',
                f'right = {toml_string(case["right"])}',
                'truth = "eq"',
                f'equivalence = {toml_string(case["equivalence"])}',
                "input_pairs = [",
                *[f"  {toml_string(pair)}," for pair in case["input_pairs"]],
                "]",
                "output_pairs = [",
                *[f"  {toml_string(pair)}," for pair in case["output_pairs"]],
                "]",
                f'qbircks_compatible = {str(case["qbircks_compatible"]).lower()}',
                f'source_left = {toml_string(case["source_left"])}',
                f'source_right = {toml_string(case["source_right"])}',
                "",
            ]
        )
    atomic_write(DEST / "manifest.toml", "\n".join(lines))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--timeout", type=int, default=7200)
    parser.add_argument("--memory-gib", type=float, default=6)
    parser.add_argument("--repair", action="store_true")
    args = parser.parse_args()

    STATE.mkdir(parents=True, exist_ok=True)
    if args.repair:
        records = json.loads((STATE / "status.json").read_text(encoding="utf-8"))
        items = []
        for record in records:
            if record["status"] != "completed":
                items.append(
                    (record["suite"], int(record["id"].rsplit("-", 1)[1]), record["source"])
                )
        records_by_id = {record["id"]: record for record in records}
    else:
        items = []
        for suite in SUITES:
            items.extend(
                (suite, index, source) for index, source in enumerate(source_paths(suite), 1)
            )
        records = []
        records_by_id = {}

    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(materialize, item, args.timeout, args.memory_gib): item for item in items
        }
        for completed, future in enumerate(as_completed(futures), 1):
            item = futures[future]
            try:
                record = future.result()
            except Exception as exc:
                suite, index, source = item
                record = {
                    "id": f"sqbricks-{suite}-{index:04d}",
                    "suite": suite,
                    "source": source,
                    "status": "error",
                    "message": f"{type(exc).__name__}: {exc}",
                }
            records_by_id[record["id"]] = record
            records = list(records_by_id.values())
            atomic_write(
                STATE / "status.json",
                json.dumps(sorted(records, key=lambda row: row["id"]), indent=2) + "\n",
            )
            print(
                f'[{completed}/{len(items)}] {record["id"]} {record["status"]}', flush=True
            )

    successful = sorted(
        (record for record in records if record["status"] == "completed"),
        key=lambda row: (SUITES.index(row["suite"]), row["id"]),
    )
    for record in successful:
        record["source_left"], record["source_right"] = case_sources(
            record["suite"], record["source"]
        )
    render_manifest(successful)
    summary = {
        "requested": len(records),
        "completed": len(successful),
        "missing": sum(record["status"] == "missing" for record in records),
        "errors": sum(record["status"] == "error" for record in records),
        "by_suite": {
            suite: sum(record["status"] == "completed" and record["suite"] == suite for record in records)
            for suite in SUITES
        },
    }
    atomic_write(STATE / "summary.json", json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()

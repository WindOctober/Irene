#!/usr/bin/env python3
"""Run unchanged CaQR in a separate directory, audit interfaces, keep failures.

Conditioned reuse operations are quarantined: official validate.py ignores
instruction conditions, so 'Validation passed' alone is not semantic evidence.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from import_itertestq import ROOT, block, write


def run(command, cwd, timeout):
    start = time.monotonic()
    try:
        p = subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=timeout,
                           env={**os.environ, "OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1", "MPLCONFIGDIR": str(ROOT / "var/benchmark-sources/matplotlib")})
        return dict(status="completed" if p.returncode == 0 else "error", exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr, seconds=time.monotonic()-start)
    except subprocess.TimeoutExpired:
        return dict(status="timeout", seconds=time.monotonic()-start)


def endpoints(text, kind):
    return [f'{"quantum" if kind == "qreg" else "classical"}:{name}[{i}]'
            for name, n in re.findall(rf"\b{kind}\s+(\w+)\[(\d+)\];", text) for i in range(int(n))]


def measured_mapping(left, right, chains):
    """Track original logical lifetimes and final classical writers, not indices."""
    from qiskit import QuantumCircuit
    l, r = QuantumCircuit.from_qasm_str(left), QuantumCircuit.from_qasm_str(right)
    if any(x.operation.name == "reset" or x.operation.condition for x in l.data):
        raise ValueError("dynamic_original_requires_audit")
    lifetimes = {i: [i] for i in range(r.num_qubits)}
    visited = set()
    for chain in chains:
        if len(set(chain)) != len(chain) or visited.intersection(chain):
            raise ValueError("overlapping_reuse_chains")
        visited.update(chain)
        lifetimes[chain[0]] = chain
    positions = {i: 0 for i in lifetimes}
    lm, rm = {}, {}
    for item in l.data:
        if item.operation.name == "measure":
            lm[l.find_bit(item.clbits[0]).index] = l.find_bit(item.qubits[0]).index
    if not lm:
        raise ValueError("no_original_classical_observables")
    for item in r.data:
        if item.operation.name not in ("measure", "reset"):
            continue
        q = r.find_bit(item.qubits[0]).index
        if item.operation.name == "measure":
            rm[r.find_bit(item.clbits[0]).index] = lifetimes[q][positions[q]]
        else:
            positions[q] += 1
            if positions[q] >= len(lifetimes[q]):
                raise ValueError("extra_reset_outside_reuse_chain")
    if any(positions[i] != len(chain)-1 for i, chain in lifetimes.items()):
        raise ValueError("incomplete_reuse_chain")
    lc, rc = endpoints(left, "creg"), endpoints(right, "creg")
    pairs, used = [], set()
    for c, logical in lm.items():
        choices = [k for k, value in rm.items() if value == logical and k not in used]
        if not choices:
            raise ValueError("original_measurement_output_overwritten")
        target = c if c in choices else choices[0]
        used.add(target)
        pairs.append(f"{lc[c]}={rc[target]}")
    return pairs, {"original_final_measurements": lm, "reuse_final_measurements": rm, "physical_lifetimes": lifetimes}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--timeout", type=int, default=20)
    p.add_argument("--jobs", type=int, default=4)
    a = p.parse_args()
    repo = ROOT / "var/benchmark-sources/CaQR"
    work = ROOT / "var/benchmark-sources/caqr-generated"
    dest = ROOT / "benchmarks/caqr"
    audit_dir = ROOT / "var/benchmark-sources/import-audits/caqr"
    python = str(ROOT / "var/benchmark-sources/caqr-env/bin/python")
    work.mkdir(exist_ok=True)
    for src in repo.glob("*.py"):
        shutil.copy2(src, work / src.name)
    shutil.copytree(repo / "benchmarks", work / "benchmarks", dirs_exist_ok=True)
    (work / "output").mkdir(exist_ok=True)

    def generate(src):
        log = work / "logs" / f"{src.stem}.json"
        if log.exists():
            return json.loads(log.read_text())
        record = dict(name=src.stem, generation=run([python, "main.py", "-b", f"benchmarks/{src.name}", "-v", "0"], work, a.timeout))
        if record["generation"]["status"] == "completed":
            record["validation"] = run([python, "validate.py", src.stem], work, a.timeout)
        write(log, json.dumps(record, indent=2) + "\n")
        print(src.stem, record["generation"]["status"], flush=True)
        return record

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        records = list(pool.map(generate, sorted((repo / "benchmarks").glob("*.qasm"))))
    # The committed sample is distinct from regeneration with the current main.py.
    shipped = dict(name="bv_n10", origin="committed-example", generation={"status": "committed"}, validation=run([python, "validate.py", "bv_n10"], repo, a.timeout))
    cases = []
    for record in [shipped, *records]:
        name = record["name"]
        committed = record.get("origin") == "committed-example"
        origin = repo if committed else work
        source = repo / "benchmarks" / f"{name}.qasm"
        output = origin / "output" / f"{name}_reuse.qasm"
        cid = "caqr-" + ("committed-" if committed else "generated-") + name.replace("_", "-")
        if record["generation"]["status"] not in ("completed", "committed"):
            record["admission"] = "generation_" + record["generation"]["status"]
            continue
        left, right = source.read_text(), output.read_text()
        chainpath = origin / "output" / f"{name}_reuse_chain.txt"
        chain = [[int(x) for x in re.findall(r"\d+", line)] for line in chainpath.read_text().splitlines() if line.strip()]
        record["reuse_chain"] = chain
        map_lines = [[int(x) for x in re.findall(r"\d+", line)] for line in (origin / "output" / f"{name}_reuse_map.txt").read_text().splitlines() if line.strip()]
        if map_lines != chain:
            record["admission"] = "quarantined_map_chain_disagreement"
            continue
        if re.search(r"\bif\s*\([^)]*\)\s*(measure|reset)\b", right):
            record["admission"] = "quarantined_conditional_measure_reset"
            continue
        validation = record.get("validation", {})
        if validation.get("status") != "completed" or "Validation passed" not in validation.get("stdout", ""):
            record["admission"] = "quarantined_official_validation_failed"
            continue
        lq, rq = endpoints(left, "qreg"), endpoints(right, "qreg")
        lc, rc = endpoints(left, "creg"), endpoints(right, "creg")
        if chain:
            try:
                outputs, audit = measured_mapping(left, right, chain)
                record["logical_output_mapping"] = audit
            except ValueError as e:
                record["admission"] = "quarantined_" + str(e)
                continue
        else:
            if lq != rq or lc != rc:
                record["admission"] = "quarantined_interface_changed"
                continue
            outputs = [f"{x}={x}" for x in lq + lc]
        record["admission"] = "paired"
        for side, text in (("left", left), ("right", right)):
            write(dest / f"programs/{cid}/{side}.qasm", text)
        for suffix in ("chain", "map"):
            shutil.copy2(origin / "output" / f"{name}_reuse_{suffix}.txt", dest / f"programs/{cid}/reuse_{suffix}.txt")
        write(audit_dir / f"provenance/{cid}.json", json.dumps(record, indent=2) + "\n")
        cases.append(dict(id=cid, suite="official-committed" if committed else ("official-generated-reuse" if chain else "official-generated-no-reuse"), left=f"programs/{cid}/left.qasm", right=f"programs/{cid}/right.qasm", truth="eq", equivalence="hybrid", initial_state="zero", input_pairs=[], output_pairs=outputs, source_left=f"benchmarks/{name}.qasm", source_right=f"output/{name}_reuse.qasm", reuse_chain=f"programs/{cid}/reuse_chain.txt", reuse_map=f"programs/{cid}/reuse_map.txt"))
    header = '''schema_version = 1
program_format = "openqasm2"

[source]
id = "caqr"
name = "CaQR official outputs with audited observable mapping"
repository = "https://github.com/ruadapt/CaQR"
commit = "0b935d962bffa6e845f2b9548b768f2f558cbe18"

[normalization]
encoding = "utf-8"
line_endings = "lf"
semantic_rewrite = false

[generation]
qiskit_version = "0.45.0"
command = "python main.py -b benchmarks/X.qasm -v 0"
'''
    write(dest / "manifest.toml", header + "".join(block(c) for c in cases))
    write(audit_dir / "import-report.json", json.dumps([shipped, *records], indent=2) + "\n")
    from collections import Counter
    print("Admission:", Counter(r["admission"] for r in [shipped, *records]))


if __name__ == "__main__":
    main()

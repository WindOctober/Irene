#!/usr/bin/env python3
"""Inventory the full official artifact; materialize a reproducible first-pass suite.

Only measurement-free, reset-free pairs with equal ordered quantum registers
are admitted: a QCEC unitary NEQ must not become a closed-distribution NEQ.
Upstream numerical QCEC labels remain reference labels, not exact certificates.
No transitive equivalence or content-identity labels are inferred.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[2]
LABELS = {"equivalent": "eq", "equivalent_up_to_global_phase": "eq", "not_equivalent": "neq"}


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def header():
    return '''schema_version = 1
program_format = "openqasm2"

[source]
id = "itertestq"
name = "IterTestQ Figshare v1, stratified static-unitary first pass"
repository = "https://github.com/sola-st/IterTestQ-quantum-platform-testing"
commit = "1ee07b1abf2ca0f4b19eb8dd1b158c9f008dda21"
dataset = "https://doi.org/10.6084/m9.figshare.33016415.v1"

[normalization]
encoding = "utf-8"
line_endings = "lf"
semantic_rewrite = false
'''


def block(case):
    return "\n[[case]]\n" + "\n".join(f"{k} = {json.dumps(v)}" for k, v in case.items()) + "\n"


def static_interface(source):
    source = re.sub(r"//[^\n]*|/\*.*?\*/", "", source, flags=re.S)
    if not re.search(r"\bOPENQASM\s+2\.0\s*;", source):
        raise ValueError("not_openqasm2")
    if re.search(r"\b(measure|reset|if|opaque)\b", source):
        raise ValueError("nonunitary_or_opaque")
    if re.search(r'include\s+"(?!qelib1.inc")', source):
        raise ValueError("nonstandard_include")
    regs = re.findall(r"\bqreg\s+(\w+)\s*\[\s*(\d+)\s*\]\s*;", source)
    if not regs:
        raise ValueError("no_quantum_interface")
    return [f"quantum:{name}[{i}]" for name, n in regs for i in range(int(n))]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--archive", type=Path, default=ROOT / "var/benchmark-sources/itertestq-artifact.zip")
    p.add_argument("--per-stratum", type=int, default=2)
    a = p.parse_args()
    dest = ROOT / "benchmarks/itertestq"
    audit = ROOT / "var/benchmark-sources/import-audits/itertestq"
    inventory = ROOT / "var/benchmark-sources/itertestq-inventory.jsonl"
    counts, excluded, strata = Counter(), Counter(), Counter()
    selected, seen, cached = [], set(), {}
    with zipfile.ZipFile(a.archive) as z, inventory.open("w") as index:
        names = set(z.namelist())
        logs = sorted(n for n in names if re.search(r"/comparison[^/]*/[^/]+\.json$", n))
        for n in logs:
            data = json.loads(z.read(n))
            label = data.get("equivalence", "missing")
            counts[label if not label.startswith("error:") else "error"] += 1
            row = {"source_record": n, "qcec_result": label}
            if label not in LABELS:
                row["excluded"] = "no_definite_qcec_label"
            else:
                run = "/".join(n.split("/")[:2])
                paths = [run + "/" + x["filename"] for x in data["qasms"]]
                row.update(source_programs=paths, equivalence_class=run + "/" + Path(paths[0]).name[:7])
                try:
                    if len(paths) != 2 or any(x not in names for x in paths):
                        raise ValueError("missing_pair_program")
                    parsed = []
                    for path in paths:
                        if path not in cached:
                            s = z.read(path).decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
                            try:
                                cached[path] = (static_interface(s), None)
                            except ValueError as e:
                                cached[path] = (None, str(e))
                        interface, error = cached[path]
                        if error:
                            raise ValueError(error)
                        parsed.append(interface)
                    if parsed[0] != parsed[1]:
                        raise ValueError("nonidentical_ordered_quantum_interface")
                    key = tuple(paths)
                    if key in seen:
                        raise ValueError("repeated_source_pair")
                    seen.add(key)
                    platforms = tuple(x.get("provenance", "generator") for x in data["qasms"])
                    stratum = (n.split("/")[0], label, *platforms)
                    strata[stratum] += 1
                    row["eligible"] = True
                    if strata[stratum] <= a.per_stratum:
                        cid = f"itertestq-{len(selected)+1:04d}"
                        for side, path in zip(("left", "right"), paths):
                            write(dest / f"programs/{cid}/{side}.qasm", z.read(path).decode("utf-8").replace("\r\n", "\n").replace("\r", "\n"))
                        write(audit / f"provenance/{cid}.json", json.dumps(data, indent=2) + "\n")
                        pairs = [f"{x}={x}" for x in parsed[0]]
                        case = dict(id=cid, suite="static-unitary", left=f"programs/{cid}/left.qasm", right=f"programs/{cid}/right.qasm", truth=LABELS[label], equivalence="unitary", input_pairs=pairs, output_pairs=pairs, source_left=paths[0], source_right=paths[1], source_record=n, equivalence_class=row["equivalence_class"], qcec_result=label, truth_basis="upstream numerical QCEC verdict; not an exact Irene certificate")
                        selected.append(case)
                        row["selected_case"] = cid
                except ValueError as e:
                    row["excluded"] = str(e)
            if "excluded" in row:
                excluded[row["excluded"]] += 1
            index.write(json.dumps(row) + "\n")
    write(dest / "manifest.toml", header() + "".join(block(c) for c in selected))
    report = dict(archive=str(a.archive.relative_to(ROOT)), comparison_records=sum(counts.values()), qcec_results=dict(counts), exclusions=dict(excluded), eligible_unique_pairs=len(seen), selected_pairs=len(selected), selection="lexicographically first two distinct directed source pairs per (experiment version, exact QCEC label, left platform, right platform), static identical quantum interface only", per_stratum=a.per_stratum, selected_truth=dict(Counter(c["truth"] for c in selected)))
    write(audit / "import-report.json", json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

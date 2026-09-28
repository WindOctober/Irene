#!/usr/bin/env python3
"""Materialize official origin versus opt/gm/flip, without semantic rewrites."""
from collections import Counter
import csv
import json
from pathlib import Path
import re
import subprocess

from import_itertestq import ROOT, block, static_interface, write

REPOSITORY = "https://github.com/System-Verification-Lab/quokka-sharp-artifacts"
SUBSETS = ('algorithm', 'random/randdepscale', 'random/randqubitscale', 'random/uniform')
MODS = {'opt': '.opt.qasm', 'gm': '.gm.qasm', 'flip': '.fp.qasm'}


def main():
    source = ROOT / 'var/benchmark-sources/quokka-sharp-artifacts'
    dest = ROOT / 'benchmarks/quokka'
    audit = ROOT / 'var/benchmark-sources/import-audits/quokka'
    revision = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    evidence = {}
    for name in ('eq_checks.csv', 'compare_eqcheck.csv'):
        path = source / 'run_benchmarks/results' / name
        evidence[name] = list(csv.DictReader(path.open()))
        write(audit / 'provenance' / name, path.read_text())
    for name in ('run_benchmarks/utils.py', 'benchmark/modifications/zxopt.py',
                 'benchmark/modifications/uneuqal.sh', 'benchmark/modifications/gatemissing.py',
                 'benchmark/modifications/flip.py'):
        write(audit / 'provenance' / name, (source / name).read_text())
    cases, inventory, copied = [], [], set()
    renamed = 0
    for subset in SUBSETS:
        base = source / 'benchmark' / subset
        for left in sorted((base / 'origin').glob('*.qasm')):
            for mod, suffix in MODS.items():
                right = base / mod / (left.name + suffix)
                if not right.is_file():
                    inventory.append(dict(subset=subset, original=left.name, modification=mod, status='missing_variant'))
                    continue
                li, ri = static_interface(left.read_text()), static_interface(right.read_text())
                if len(li) != len(ri):
                    raise ValueError(f'Quantum interface width mismatch: {left} {right}')
                # PyZX flattens registers by declaration order (not by name).
                pairs = [f'{a}={b}' for a, b in zip(li, ri)]
                renamed += li != ri
                paths = []
                for path in (left, right):
                    relative = path.relative_to(source / 'benchmark')
                    local = Path('programs') / relative
                    if local not in copied:
                        write(dest / local, path.read_text())
                        copied.add(local)
                    paths.append(str(local))
                cid = 'quokka-' + re.sub('[^A-Za-z0-9-]', '-', subset + '-' + left.stem + '-' + mod)
                rows = []
                if subset == 'random/uniform':
                    match = re.fullmatch(r'random_q(\d+)_d(\d+)_s(\d+)', left.stem)
                    if match:
                        q, d, seed = map(int, match.groups())
                        rows = [dict(file='eq_checks.csv', row=i+2, record=r) for i, r in enumerate(evidence['eq_checks.csv'])
                                if (int(r['qubits']), int(r['depth']), int(r['seed']), r['mod']) == (q,d,seed,mod)]
                elif subset == 'algorithm':
                    match = re.match(r'(\w+)_(\w+)_(\w+)_(\w+)_([\w\d]+)_(\d+)$', left.stem)
                    algo = match.group(1) if match else left.stem
                    rows = [dict(file='compare_eqcheck.csv', row=i+2, record=r) for i,r in enumerate(evidence['compare_eqcheck.csv'])
                            if r['algo'] == algo and r['modification'] == mod and int(r['qubits']) == len(li)]
                prov = f'provenance/cases/{cid}.json'
                write(audit / prov, json.dumps(dict(source_left=str(left.relative_to(source)),
                      source_right=str(right.relative_to(source)), official_results=rows,
                      label_status='upstream expected label, not independently certified',
                      interface='all quantum inputs and outputs; registers flattened in declaration order'), indent=2)+'\n')
                case = dict(id=cid, suite=subset.replace('/', '-')+'-'+mod, left=paths[0], right=paths[1],
                            truth='eq' if mod == 'opt' and cid != 'quokka-algorithm-routing-nativegates-ibm-qiskit-opt0-2-opt' else 'neq', equivalence='unitary',
                            input_pairs=pairs, output_pairs=pairs,
                            source_left=str(left.relative_to(source)), source_right=str(right.relative_to(source)),
                            modification=mod, truth_basis='upstream expected '+('equivalence-preserving PyZX optimization' if mod=='opt' else 'inequivalent mutation; not independently certified'))
                cases.append(case)
                inventory.append(dict(id=cid, subset=subset, modification=mod, status='included', official_result_rows=len(rows)))
    assert len({c['id'] for c in cases}) == len(cases)
    header = f'''schema_version = 1
program_format = "openqasm2"

[source]
id = "quokka"
name = "Quokka-Sharp official algorithm and random optimization/mutation pairs"
repository = "{REPOSITORY}"
commit = "{revision}"

[normalization]
encoding = "utf-8"
line_endings = "lf"
semantic_rewrite = false
'''
    write(dest / 'manifest.toml', header + ''.join(block(c) for c in cases))
    report = dict(repository=REPOSITORY, commit=revision, paired_cases=len(cases),
                  unique_program_files=len(copied), truth=dict(Counter(c['truth'] for c in cases)),
                  modifications=dict(Counter(c['modification'] for c in cases)),
                  suites=dict(Counter(c['suite'] for c in cases)), flattened_register_pairs=renamed,
                  exclusions='shift4, shift7, compound flip+gm, unrelated artifact collections; no all-pairs expansion',
                  inventory=inventory)
    write(audit / 'import-report.json', json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='inventory'}, indent=2))


if __name__ == '__main__':
    main()

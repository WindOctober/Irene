#!/usr/bin/env python3
"""Isolated baseline reruns; one mode per job, one global concurrency limit.

Keeps historical canonical runs untouched. Resource-pressure attempts are retained
but retried, never counted as solver failures. No Irene execution is performed.
"""
import argparse
from collections import Counter, deque
import hashlib
import fcntl
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import psutil

import run as core

MANIFESTS = ('sqbricks/manifest.toml', 'sqbricks/generated/manifest.toml',
             'openqasm3-programs/manifest.toml', 'qubit-reuse/manifest.toml',
             'itertestq/manifest.toml', 'caqr/manifest.toml', 'quokka/manifest.toml')
GIB = 1024 ** 3


def save(path, data):
    core.atomic_write(path, json.dumps(data, indent=2, sort_keys=True) + '\n')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sanitize_logs(folder):
    for name in ('stdout.log', 'stderr.log'):
        log = folder/name
        if log.exists():
            log.write_text(core.portable_text(log.read_text(errors='replace'), core.ROOT))


def plan(case_filter=None):
    jobs = []
    for rel in MANIFESTS:
        manifest = core.BENCHMARKS / rel
        for case in core.load_cases(manifest):
            if case_filter and case['id'] not in case_filter:
                continue
            for tool in ('sqbricks', 'qcec', 'veriqc'):
                for variant in core.variants(tool, case):
                    jobs.append(dict(tool=tool, variant=variant, case=dict(case),
                                     collection=core.collection_name(manifest),
                                     manifest=str(manifest.relative_to(core.ROOT))))
    return jobs


def missing_jobs(jobs, previous, timeout, memory_gib):
    """Reuse terminal attempts only for identical inputs, semantics and limits."""
    hashes = json.loads((previous/'provenance/input-sha256.json').read_text())
    rows = {}
    for path in previous.glob('*/*/cases/*/*/result.json'):
        row = json.loads(path.read_text())
        rows[(row['tool'], row['collection'], row['case_id'], row['variant'])] = row
    current = {}
    missing = []
    for job in jobs:
        case = job['case']
        row = rows.get((job['tool'], job['collection'], case['id'], job['variant']))
        same = bool(row) and row.get('status') in ('completed', 'timeout', 'memory_limit', 'unsupported', 'error')
        if same:
            same = row.get('timeout_sec') == timeout and row.get('memory_limit_bytes') == int(memory_gib*GIB)
            same = same and all(row.get(k) == case.get(k) for k in
                ('truth', 'equivalence', 'input_pairs', 'output_pairs', 'initial_state'))
        if same:
            for side in ('left_abs', 'right_abs'):
                path = case[side]
                if path not in current: current[path] = digest(path)
                recorded = hashes.get(path, hashes.get(core.portable_text(path, core.ROOT)))
                same = same and recorded == current[path]
        if not same: missing.append(job)
    return missing


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--label', required=True)
    parser.add_argument('--jobs', type=int, default=24)
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--memory-gib', type=float, default=6)
    parser.add_argument('--qcec-threads', type=int, default=2)
    parser.add_argument('--case', action='append')
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--previous', type=Path)
    parser.add_argument('--job-list', required=True, type=Path)
    parser.add_argument('--admit-memory-gib', type=float, default=62)
    parser.add_argument('--total-memory-gib', type=float, default=64)
    args = parser.parse_args()
    if not core.re.fullmatch(r'[a-z0-9][a-z0-9-]*', args.label):
        parser.error('label must be a lowercase path-safe name')
    if min(args.jobs, args.timeout, args.memory_gib, args.qcec_threads) <= 0:
        parser.error('resource limits must be positive')
    if not 0 < args.admit_memory_gib < args.total_memory_gib:
        parser.error('invalid global memory thresholds')
    jobs = json.loads(args.job_list.read_text())
    checked_inputs = {}
    for job in jobs:
        for side in ('left_abs', 'right_abs'):
            relative = job['case'][side]
            path = (core.BENCHMARKS/relative).resolve()
            if not path.is_relative_to(core.BENCHMARKS.resolve()): parser.error('unsafe input path')
            if path not in checked_inputs: checked_inputs[path] = digest(path)
            if checked_inputs[path] != job['input_hashes'][side]: parser.error('remote input differs: '+str(path))
            job['case'][side] = str(path)
    if args.case: jobs = [j for j in jobs if j['case']['id'] in args.case]
    counts = dict(Counter(j['tool'] + '/' + j['variant'] for j in jobs))
    if args.plan:
        print(json.dumps({'tasks': len(jobs), 'pairs': len({j['case']['id'] for j in jobs}),
                          'by_collection': dict(Counter(j['collection'] for j in jobs)), 'by_configuration': counts}))
        return
    dest = core.EXPERIMENTS / 'campaigns' / args.label
    # New campaign only: never silently reuse 7200-second historical records.
    dest.mkdir(parents=True, exist_ok=False)
    lock = (dest/'run.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    runtime = core.RUNTIME / args.label
    runtime.mkdir(parents=True, exist_ok=False)
    provenance = dest / 'provenance'
    provenance.mkdir()
    for path in [Path(__file__), Path(core.__file__), *core.WORKERS.glob('*_worker.py')]:
        shutil.copy2(path, provenance / path.name)
    # Freeze worker implementations for the entire background campaign.
    core.WORKERS = provenance
    versions = {}
    for tool, repo in [('sqbricks', 'tools/qbricks.github.io'),
                       ('qcec', 'tools/qcec'),
                       ('veriqc', 'tools/EC-for-Dynamic-Quantum-Circuits')]:
        versions[tool] = subprocess.check_output(
            ['git', '-C', str(core.ROOT / repo), 'rev-parse', 'HEAD'], text=True).strip()
    inputs = {}
    for job in jobs:
        for path in [core.ROOT / job['manifest'], Path(job['case']['left_abs']),
                     Path(job['case']['right_abs'])]:
            if str(path) not in inputs:
                inputs[str(path)] = digest(path)
    save(provenance / 'input-sha256.json', inputs)
    copied = {}
    for job in jobs:
        for side in ('left_abs', 'right_abs'):
            path = Path(job['case'][side])
            if path not in copied:
                target = provenance/'inputs'/path.relative_to(core.BENCHMARKS)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, target)
                copied[path] = str(target)
            job['case'][side] = copied[path]
    save(dest/'jobs.json', jobs)
    config = dict(vars(args), timeout_kind='wall-clock including preprocessing',
                  memory_kind='sampled process-tree RSS', memory_limit_bytes=int(args.memory_gib*GIB),
                  memory_pressure_policy='host used=MemTotal-MemAvailable; pause at admission threshold; retry at total threshold',
                  sqbricks_modes_independent=True, cpu_affinity=None,
                  blas_threads=1, tool_commits=versions, expected_tasks=len(jobs),
                  by_configuration=counts,
                  logical_cpus=os.cpu_count(), started_at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
    config['previous'] = str(args.previous)
    config['job_list'] = str(args.job_list)
    config['cpu_policy'] = 'nice 10; inherited affinity; adaptive admission based on external CPU use, shrink by draining'
    save(dest / 'config.json', config)
    queue = deque(jobs)
    active, rows, attempts = {}, [], Counter()
    concurrency = min(8, args.jobs)
    own_process = psutil.Process()
    pool = sorted(os.sched_getaffinity(0))
    psutil.cpu_percent(percpu=True)
    cpu_previous = {}
    cpu_time = time.monotonic()
    cpu_observation = {}
    stopping = False
    state = 'running'
    started = time.monotonic()
    last_checkpoint = 0

    def stop(signum, frame):
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def checkpoint():
        groups = {}
        for row in rows:
            groups.setdefault((row['tool'], row['collection']), []).append(row)
        for (tool, collection), items in groups.items():
            folder = dest / tool / collection
            core.atomic_write(folder / 'results.jsonl', ''.join(json.dumps(r, sort_keys=True)+'\n' for r in items))
            save(folder / 'summary.json', dict(core.summarize(items), tool=tool, collection=collection))
        save(dest / 'progress.json', dict(state=state, pid=os.getpid(),
             expected=len(jobs), completed=len(rows), pending=len(queue), active=len(active),
             current_concurrency=concurrency, max_concurrency=args.jobs,
             cpu_observation=cpu_observation, available_memory_gib=round(core.read_mem_available()/GIB,2),
             elapsed_sec=round(time.monotonic()-started, 2),
             updated_at=time.strftime('%Y-%m-%dT%H:%M:%S%z'),
             statuses=dict(Counter(r['status'] for r in rows)),
             configurations=dict(Counter(r['tool']+'/'+r['variant'] for r in rows)),
             active_jobs=[dict(tool=v['job']['tool'], variant=v['job']['variant'],
                               case_id=v['job']['case']['id'], pid=pid) for pid,v in active.items()]))

    def launch(job):
        case, tool, variant = job['case'], job['tool'], job['variant']
        key = (tool, case['id'], variant)
        attempts[key] += 1
        jobdir = runtime / tool / case['id'] / variant
        attempt = jobdir / str(attempts[key])
        attempt.mkdir(parents=True)
        (attempt / 'tmp').mkdir()
        casefile = attempt / 'job.json'
        save(casefile, dict(case, sqbricks_variants=[variant]))
        command = core.worker_command(tool, casefile, attempt, case['id'], args.qcec_threads)
        command = ['nice', '-n', '10', 'prlimit', f'--as={config["memory_limit_bytes"]}', '--', *command]
        env = dict(os.environ, PYTHONUNBUFFERED='1', PYTHONDONTWRITEBYTECODE='1',
                   TMPDIR=str(attempt / 'tmp'), OMP_NUM_THREADS='1',
                   OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1', NUMEXPR_NUM_THREADS='1')
        out = (attempt / 'stdout.log').open('wb')
        err = (attempt / 'stderr.log').open('wb')
        try:
            process = subprocess.Popen(command, cwd=core.ROOT, env=env,
                stdin=subprocess.DEVNULL, stdout=out, stderr=err, start_new_session=True)
        finally:
            out.close()
            err.close()
        active[process.pid] = dict(process=process, job=job, attempt=attempt,
            start=time.monotonic(), peak=0, current=0, observed={}, reason=None, command=command)

    def kill(item, reason):
        item['reason'] = reason
        core.remember_descendants(item['process'].pid, item['observed'])
        core.signal_process_group(item['process'].pid, signal.SIGKILL)
        core.signal_observed(item['observed'], signal.SIGKILL)

    def finish(item):
        job, attempt = item['job'], item['attempt']
        tool, variant, case = job['tool'], job['variant'], job['case']
        core.signal_process_group(item['process'].pid, signal.SIGKILL)
        core.signal_observed(item['observed'], signal.SIGKILL)
        wall = time.monotonic()-item['start']
        sanitize_logs(attempt)
        if item['reason'] == 'resource_pressure':
            save(attempt/'interrupted.json', dict(reason='resource_pressure', wall_time_sec=wall,
                 peak_rss_bytes=item['peak'], counted_as_solver_result=False))
            queue.append(job)
            return
        result = None
        if item['reason'] is None:
            for line in (attempt/'stdout.log').read_text(errors='replace').splitlines():
                if line.startswith('RESULT_JSON='):
                    try:
                        payload = json.loads(line[len('RESULT_JSON='):])
                        result = next(r for r in payload['results'] if r['variant']==variant)
                    except (ValueError, KeyError, StopIteration, TypeError):
                        pass
        if result is None:
            result = dict(status=item['reason'] or 'error', verdict=None,
                          message=item['reason'] or 'worker produced no normalized result')
        folder = dest / tool / job['collection']
        casedir = folder / 'cases' / case['id'] / variant
        casedir.mkdir(parents=True)
        for name in ('stdout.log', 'stderr.log'):
            shutil.copy2(attempt/name, casedir/name)
        verdict = result.get('verdict')
        row = dict(result, schema_version=1, tool=tool, variant=variant,
            collection=job['collection'], case_id=case['id'], suite=case['suite'],
            truth=case['truth'], equivalence=case['equivalence'], left=case['left'], right=case['right'],
            input_pairs=case['input_pairs'], output_pairs=case['output_pairs'],
            initial_state=case.get('initial_state'),
            matches_truth=verdict==case['truth'] if verdict in ('eq','neq') else None,
            wall_time_sec=round(wall,6), peak_rss_bytes=item['peak'],
            exit_code=item['process'].returncode, tool_commit=versions[tool],
            timeout_sec=args.timeout, memory_limit_bytes=config['memory_limit_bytes'],
            qcec_threads=args.qcec_threads if tool=='qcec' else None,
            stdout_path=str((casedir/'stdout.log').relative_to(folder)),
            stderr_path=str((casedir/'stderr.log').relative_to(folder)),
            command=item['command'], campaign=args.label)
        save(casedir/'result.json', row)
        rows.append(row)
        print(f"[{len(rows)}/{len(jobs)}] {tool}/{variant} {case['id']} {row['status']} {verdict} {wall:.2f}s", flush=True)

    print(core.portable_text(json.dumps(config), core.ROOT), flush=True)
    try:
        checkpoint()
        while queue or active:
            now = time.monotonic()
            if now-cpu_time >= 5:
                elapsed = now-cpu_time
                percpu = psutil.cpu_percent(percpu=True)
                samples = {}
                own_seconds = 0.0
                for proc in own_process.children(recursive=True):
                    try:
                        times = proc.cpu_times()
                        key = (proc.pid, proc.create_time())
                        seconds = times.user+times.system
                        samples[key] = seconds
                        own_seconds += max(0, seconds-cpu_previous.get(key, seconds))
                    except (psutil.NoSuchProcess, psutil.AccessDenied): pass
                own_cores = own_seconds/elapsed
                pool_busy = sum(percpu[c] for c in pool)/100
                external = max(0, pool_busy-own_cores)
                # Two CPU threads for QCEC, one for other modes: reserve capacity
                # using the actual active configuration, then conservatively 1.25/job.
                target = max(1, min(args.jobs, int(max(0,len(pool)-external-4)/1.25)))
                concurrency = min(target, concurrency+2)
                cpu_observation = dict(pool=pool, busy_cores=round(pool_busy,2),
                    own_cores=round(own_cores,2), external_cores=round(external,2), target=target)
                cpu_previous, cpu_time = samples, now
            if (dest/'STOP').exists(): stopping = True
            if stopping:
                state = 'interrupted'
                break
            for pid, item in list(active.items()):
                core.remember_descendants(pid, item['observed'])
                item['current'] = core.rss_bytes(pid)
                item['peak'] = max(item['peak'], item['current'])
                if item['process'].poll() is None and not item['reason']:
                    if item['current'] > config['memory_limit_bytes']:
                        kill(item, 'memory_limit')
                    elif time.monotonic()-item['start'] >= args.timeout:
                        kill(item, 'timeout')
                if item['process'].poll() is not None:
                    finish(item)
                    del active[pid]
            total = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemTotal:')))*1024
            used = total - core.read_mem_available()
            if used >= args.total_memory_gib*GIB:
                candidates = [v for v in active.values() if not v['reason']]
                if candidates:
                    victim = max(candidates, key=lambda v: v['current'])
                    kill(victim, 'resource_pressure')
                    print(f'Memory-pressure retry; concurrency now {concurrency}', flush=True)
            elif queue and len(active)<concurrency and used<args.admit_memory_gib*GIB:
                launch(queue.popleft())
            if time.monotonic()-last_checkpoint>5:
                checkpoint()
                last_checkpoint = time.monotonic()
            time.sleep(0.1)
        if not stopping:
            assert len(rows)==len(jobs)
            state = 'complete'
    except BaseException:
        state = 'failed'
        raise
    finally:
        for item in active.values():
            kill(item, 'interrupted')
            item['process'].wait(timeout=5)
            sanitize_logs(item['attempt'])
        active.clear()
        checkpoint()
        save(dest/'completion.json', dict(state=state, completed=len(rows), expected=len(jobs),
             finished_at=time.strftime('%Y-%m-%dT%H:%M:%S%z')))
    print(f'{state}: {len(rows)}/{len(jobs)}', flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Bounded 24-slot representation census; no promotion into canonical results."""
import argparse
import concurrent.futures
import csv
import gzip
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import threading
import time
from collections import Counter

import psutil
import tomli

from portable import portable_text

ROOT = Path(os.environ.get("IRENE_ARTIFACT_ROOT", Path(__file__).resolve().parents[2])).resolve()

MANIFESTS = ("sqbricks/manifest.toml", "sqbricks/generated/manifest.toml",
             "openqasm3-programs/manifest.toml", "qubit-reuse/manifest.toml",
             "itertestq/manifest.toml", "caqr/manifest.toml", "quokka/manifest.toml")
GIB = 1024**3
STOP = threading.Event()


def save(path, data):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(portable_text(json.dumps(data, indent=2) + "\n", ROOT))
    temporary.replace(path)


def analyzer(path):
    spec = importlib.util.spec_from_file_location("representation_stats", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_process(command, folder, env, timeout, memory, affinity):
    command = ["nice", "-n", "10", "taskset", "-c", ",".join(map(str, affinity)),
               "prlimit", f"--as={memory}", "--", *command]
    started = time.monotonic()
    observed = {}
    reason, peak = None, 0
    with (folder / "stdout.log").open("wb") as out, (folder / "stderr.log").open("wb") as err:
        proc = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                                env=env, cwd=ROOT, start_new_session=True)
        parent = psutil.Process(proc.pid)
        try:
            while proc.poll() is None:
                current = 0
                try:
                    for child in [parent, *parent.children(recursive=True)]:
                        observed[(child.pid, child.create_time())] = child
                        current += child.memory_info().rss
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    pass
                peak = max(peak, current)
                if STOP.is_set(): reason = "interrupted"
                elif time.monotonic() - started >= timeout: reason = "timeout"
                elif current > memory: reason = "memory_limit"
                elif psutil.virtual_memory().available < 6 * GIB: reason = "host_memory_pressure"
                elif shutil.disk_usage(folder).free < 12 * GIB: reason = "disk_pressure"
                if reason:
                    break
                time.sleep(0.2)
        finally:
            # Solver descendants can have their own process groups.
            for child in reversed(list(observed.values())):
                try:
                    if child.is_running(): child.kill()
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    pass
            if proc.poll() is None:
                try: os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError: pass
            proc.wait()
    for name in ("stdout.log", "stderr.log"):
        log = folder / name
        log.write_text(portable_text(log.read_text(errors="replace"), ROOT))
    return {"status": reason or ("completed" if proc.returncode == 0 else "error"),
            "exit_code": proc.returncode, "wall_time_sec": time.monotonic()-started,
            "peak_sampled_tree_rss_bytes": peak, "command": command}


def empty_case(path, message):
    return {"path": str(path), "header": None, "footer": None,
            "counts": {"snapshots": 0, "exact": 0, "expansion_budget_exceeded": 0},
            "budget_reasons": {}, "error": message, "paired_complete": False,
            "paired_observed_maxima": None}


def main():
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path)
    parser.add_argument("--label")
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--analysis-timeout", type=int, default=600)
    parser.add_argument("--case", action="append")
    parser.add_argument("--analyze-one", nargs=3, metavar=("ANALYZER", "TRACE", "OUTPUT"))
    args = parser.parse_args()
    if args.analyze_one:
        source, trace, output = args.analyze_one
        save(Path(output), analyzer(source).analyze_file(trace))
        return
    if not args.root or not args.label or args.jobs < 1:
        parser.error("root, label and positive jobs are required")
    if not all(c.isalnum() or c in "-_" for c in args.label):
        parser.error("unsafe label")
    root = args.root.resolve()
    ROOT = root
    dest = root / "experiments" / "campaigns" / args.label
    dest.mkdir(parents=True, exist_ok=False)
    provenance = dest / "provenance"
    provenance.mkdir()
    worker = root / "tools/irene-experiment-worker"
    for source, target in [
        (worker / "target/release/irene-experiment-worker", "irene-experiment-worker"),
        (worker / "src/main.rs", "worker-main.rs"),
        (worker / "Cargo.lock", "worker-Cargo.lock"),
        (root / "scripts/representation_stats.py", "representation_stats.py"),
        (root / "src/symbolic/boolean/statistics.rs", "statistics.rs"),
        (Path(__file__), "run_representation_campaign.py"),
        (Path(__file__).with_name("portable.py"), "portable.py"),
    ]:
        shutil.copy2(source, provenance / target)
    # Freeze the actual dirty source used for this build, excluding build caches.
    shutil.copytree(root / "src", provenance / "irene-src")
    shutil.copy2(root / "Cargo.toml", provenance / "irene-Cargo.toml")
    shutil.copy2(root / "Cargo.lock", provenance / "irene-Cargo.lock")
    jobs = []
    benchmarks = root / "benchmarks"
    for name in MANIFESTS:
        manifest = benchmarks / name
        data = tomli.loads(manifest.read_text())
        collection = "-".join(Path(name).parent.parts)
        saved_manifest = provenance / "inputs" / name
        saved_manifest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(manifest, saved_manifest)
        for original in data["case"]:
            if args.case and original["id"] not in args.case:
                continue
            case = dict(original)
            if not all(c.isalnum() or c in "-_" for c in case["id"]):
                raise ValueError("unsafe case id")
            for side in ("left", "right"):
                source = (manifest.parent / case[side]).resolve()
                relative = source.relative_to(benchmarks.resolve())
                target = provenance / "inputs" / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.exists(): shutil.copy2(source, target)
                case[side + "_abs"] = str(target)
            jobs.append({"collection": collection, "case": case})
    if len({(j["collection"], j["case"]["id"]) for j in jobs}) != len(jobs):
        raise ValueError("duplicate cases")
    pool = sorted(os.sched_getaffinity(0))
    config = {"jobs": args.jobs, "expected": len(jobs), "timeout_sec": args.timeout,
              "analysis_timeout_sec": args.analysis_timeout, "memory_limit_bytes": 6*GIB,
              "memory_kind": "RLIMIT_AS per process plus monitored tree RSS",
              "cores_per_job": min(10, len(pool)), "sampling_every": 1,
              "started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "canonical_results_modified": False,
              "by_collection": dict(Counter(j["collection"] for j in jobs)),
              "statistics_scope": "HPS checkpoint Boolean expressions, not source heap or process peak",
              "anf_budgets": {"max_terms": 100000, "max_work": 2000000,
                              "max_live_entries": 500000, "max_live_variable_refs": 2000000}}
    save(dest / "config.json", config)
    save(dest / "jobs.json", jobs)
    print(json.dumps(config), flush=True)
    signal.signal(signal.SIGTERM, lambda *_: STOP.set())
    signal.signal(signal.SIGINT, lambda *_: STOP.set())
    stats = analyzer(provenance / "representation_stats.py")
    active, lock = {}, threading.Lock()
    rows, census = [], []
    started = time.monotonic()

    def run_one(index, job):
        case = job["case"]
        folder = dest / "cases" / job["collection"] / case["id"]
        folder.mkdir(parents=True)
        trace = folder / "trace.jsonl"
        save(folder / "job.json", case)
        if STOP.is_set():
            return {"case_id": case["id"], "status": "not_started"}, empty_case(trace, "interrupted")
        env = {k: v for k, v in os.environ.items() if not k.startswith("IRENE_")}
        env.update(IRENE_ARTIFACT_ROOT=str(root), IRENE_REPRESENTATION_STATS=str(trace), IRENE_REPRESENTATION_STATS_EVERY="1",
                   IRENE_DAG_MODE="dag_interval", OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1",
                   MKL_NUM_THREADS="1", PYTHONUNBUFFERED="1", PYTHONDONTWRITEBYTECODE="1")
        temporary = folder / "tmp"
        temporary.mkdir()
        env["TMPDIR"] = str(temporary)
        affinity = [pool[(index + n) % len(pool)] for n in range(min(10, len(pool)))]
        with lock: active[case["id"]] = "verification"
        verification = run_process([str(provenance / "irene-experiment-worker"), str(folder / "job.json")],
                                   folder, env, args.timeout, 6*GIB, affinity)
        payload = None
        for line in (folder / "stdout.log").read_text(errors="replace").splitlines():
            if line.startswith("RESULT_JSON="):
                try: payload = json.loads(line[len("RESULT_JSON="):])
                except ValueError: pass
        record = {"case_id": case["id"], "collection": job["collection"],
                  "verification": verification, "worker_result": payload}
        analysis_dir = folder / "analysis"
        analysis_dir.mkdir()
        with lock: active[case["id"]] = "anf_analysis"
        result_path = folder / "representation.json"
        analysis_run = run_process([sys.executable, "-B", str(provenance / "run_representation_campaign.py"),
                                   "--analyze-one", str(provenance / "representation_stats.py"),
                                   str(trace), str(result_path)], analysis_dir, env,
                                  args.analysis_timeout, 6*GIB, affinity)
        record["analysis"] = analysis_run
        result = json.loads(result_path.read_text()) if result_path.exists() else empty_case(trace, analysis_run["status"])
        # A killed verifier's earlier complete subtraces must not count as a whole case.
        if verification["status"] != "completed":
            result["paired_complete"] = False
            result["paired_observed_maxima"] = None
            result["verification_incomplete"] = verification["status"]
        save(result_path, result)
        if trace.exists():
            with lock: active[case["id"]] = "compressing"
            compressed = trace.with_suffix(".jsonl.gz")
            with trace.open("rb") as source, gzip.open(compressed, "wb", compresslevel=1) as target:
                shutil.copyfileobj(source, target, 1024*1024)
            # Only this task's raw snapshot is removed; the full trace is retained losslessly.
            trace.unlink()
            record["trace_gzip"] = str(compressed)
        save(folder / "result.json", record)
        with lock: active.pop(case["id"], None)
        return record, result

    def progress(state):
        with lock: running = dict(active)
        save(dest / "progress.json", {"state": state, "pid": os.getpid(), "expected": len(jobs),
             "completed": len(rows), "active": len(running), "active_jobs": running,
             "parallelism": args.jobs, "paired_complete": sum(c["paired_complete"] for c in census),
             "elapsed_sec": time.monotonic()-started, "updated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    state = "failed"
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(run_one, index, job): job for index, job in enumerate(jobs)}
            while futures:
                done, _ = concurrent.futures.wait(futures, timeout=3, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    job = futures.pop(future)
                    try:
                        record, result = future.result()
                    except Exception as error:
                        record = {"case_id": job["case"]["id"], "status": "runner_error", "error": repr(error)}
                        result = empty_case(job["case"]["id"], repr(error))
                        with lock: active.pop(job["case"]["id"], None)
                    rows.append(record); census.append(result)
                    print(f"[{len(rows)}/{len(jobs)}] {job['case']['id']} paired={result['paired_complete']} snapshots={result['counts']['snapshots']}", flush=True)
                progress("stopping" if STOP.is_set() else "running")
        summary = stats.aggregate(census)
        save(dest / "summary.json", {"schema_version": 1, "config": config, "summary": summary, "cases": census})
        save(dest / "results.json", rows)
        means = summary["mean_per_case_observed_maxima"]
        with (dest / "table.csv").open("w", newline="") as output:
            writer = csv.writer(output)
            writer.writerow(["XAG nodes", "XAG packed storage (bytes)", "Shared ANF monomials", "Shared ANF storage (estimated bytes)"])
            writer.writerow([means[c] for c in ("xag_nodes", "xag_packed_bytes", "anf_unique_monomials", "anf_shared_estimated_bytes")])
        state = "interrupted" if STOP.is_set() else "complete"
    finally:
        progress(state)
        save(dest / "completion.json", {"state": state, "completed": len(rows), "expected": len(jobs),
                                        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    print(f"{state}: {len(rows)}/{len(jobs)}", flush=True)


if __name__ == "__main__":
    main()

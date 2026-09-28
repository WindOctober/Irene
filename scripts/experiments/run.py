#!/usr/bin/env python3
import argparse
import asyncio
import json
import math
import os
import re
import shutil
import signal
import subprocess
import time
from collections import Counter, defaultdict
from pathlib import Path

import tomli

from portable import portable_text


ROOT = Path(__file__).resolve().parents[2]
BENCHMARKS = ROOT / "benchmarks"
EXPERIMENTS = ROOT / "experiments"
RUNTIME = ROOT / "var" / "experiments"
WORKERS = Path(__file__).resolve().parent / "workers"
DEFAULT_MANIFEST = BENCHMARKS / "sqbricks" / "manifest.toml"
IRENE_MEMORY_MAX_BYTES = 2 * 1024**3
MAX_JOBS = 8
WORKER_ANALYSIS_FIELDS = frozenset(
    {
        "ablation",
        "kernel_terms",
        "left_nodes",
        "message",
        "native_result",
        "right_nodes",
        "solver_queries",
        "tool_time_sec",
    }
)


def atomic_write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(portable_text(text, ROOT), encoding="utf-8")
    os.replace(temporary, path)


def atomic_write_bytes(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def read_mem_available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


def descendants(pid):
    found = {pid}
    queue = [pid]
    while queue:
        current = queue.pop()
        children = Path(f"/proc/{current}/task/{current}/children")
        try:
            values = [int(value) for value in children.read_text().split()]
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            values = []
        for child in values:
            if child not in found:
                found.add(child)
                queue.append(child)
    return found


def rss_bytes(pid):
    total = 0
    for process in descendants(pid):
        try:
            for line in Path(f"/proc/{process}/status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1]) * 1024
                    break
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return total


def process_identity(pid):
    try:
        # Field 22 is the process start time. It prevents cleanup from signaling
        # an unrelated process if a short-lived descendant's PID is reused.
        return Path(f"/proc/{pid}/stat").read_text().split()[21]
    except (FileNotFoundError, ProcessLookupError, PermissionError, IndexError):
        return None


def remember_descendants(pid, observed):
    for child in descendants(pid):
        identity = process_identity(child)
        if identity is not None:
            observed[child] = identity


def signal_observed(observed, sig):
    for pid, identity in tuple(observed.items()):
        if process_identity(pid) != identity:
            continue
        try:
            os.kill(pid, sig)
        except (ProcessLookupError, PermissionError):
            pass


def signal_process_group(pid, sig):
    try:
        os.killpg(pid, sig)
    except (ProcessLookupError, PermissionError):
        pass


async def cleanup_process_tree(process, observed, grace_sec):
    remember_descendants(process.pid, observed)
    signal_process_group(process.pid, signal.SIGTERM)
    signal_observed(observed, signal.SIGTERM)
    try:
        await asyncio.wait_for(process.wait(), timeout=grace_sec)
    except asyncio.TimeoutError:
        pass
    await asyncio.sleep(min(grace_sec, 0.1))
    signal_process_group(process.pid, signal.SIGKILL)
    signal_observed(observed, signal.SIGKILL)
    try:
        await asyncio.wait_for(process.wait(), timeout=1)
    except asyncio.TimeoutError:
        pass


def load_cases(manifest):
    with manifest.open("rb") as handle:
        data = tomli.load(handle)
    base = manifest.parent
    cases = []
    for case in data["case"]:
        item = dict(case)
        item["left_abs"] = str((base / case["left"]).resolve())
        item["right_abs"] = str((base / case["right"]).resolve())
        cases.append(item)
    return cases


def collection_name(manifest):
    try:
        relative = manifest.parent.resolve().relative_to(BENCHMARKS.resolve())
    except ValueError as error:
        raise ValueError("the manifest must be below benchmarks/") from error
    name = "-".join(relative.parts)
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", name):
        raise ValueError(f"invalid benchmark collection name: {name}")
    return name


def commits():
    revisions = {}
    for name, repo in {
        "irene": ROOT,
        "qcec": ROOT / "tools/qcec",
        "veriqc": ROOT / "tools/EC-for-Dynamic-Quantum-Circuits",
        "sqbricks": ROOT / "tools/qbricks.github.io",
    }.items():
        revisions[name] = "source-archive"
        if not (repo / ".git").exists():
            continue
        try:
            revision = subprocess.check_output(
                ["git", "-C", str(repo), "rev-parse", "--short", "HEAD"],
                text=True, stderr=subprocess.DEVNULL,
            ).strip()
            dirty = subprocess.check_output(
                ["git", "-C", str(repo), "status", "--porcelain"],
                text=True, stderr=subprocess.DEVNULL,
            ).strip()
            revisions[name] = revision + ("-dirty" if dirty else "")
        except (OSError, subprocess.CalledProcessError):
            pass
    return revisions


def variants(tool, case):
    if tool == "sqbricks":
        return ("par",) if case["suite"] == "owm-vs-tele" else ("seq", "par")
    if tool == "irene":
        return ("symbolic",)
    return ("dynamic",) if tool == "qcec" else ("tdd",)


def worker_command(tool, case_file, runtime_dir, case_id, qcec_threads):
    if tool == "irene":
        return [
            str(ROOT / "tools/irene-experiment-worker/target/release/irene-experiment-worker"),
            str(case_file),
        ]
    if tool == "qcec":
        return [
            str(ROOT / "tools/qcec/envs/python/bin/python"),
            str(WORKERS / "qcec_worker.py"),
            str(case_file),
            "--threads",
            str(qcec_threads),
        ]
    if tool == "veriqc":
        return [
            str(ROOT / "tools/EC-for-Dynamic-Quantum-Circuits/envs/python/bin/python"),
            str(WORKERS / "veriqc_worker.py"),
            str(case_file),
            "--repo",
            str(ROOT / "tools/EC-for-Dynamic-Quantum-Circuits"),
        ]
    return [
        "python3",
        str(WORKERS / "sqbricks_worker.py"),
        str(case_file),
        "--repo",
        str(ROOT / "tools/qbricks.github.io/Artifacts/SQbricks/SQbricks"),
        "--tmp",
        str(runtime_dir / "tmp" / case_id),
    ]


def load_existing(run_dir):
    records = []
    for path in sorted((run_dir / "cases").glob("*/*/result.json")):
        records.append(json.loads(path.read_text(encoding="utf-8")))
    return records


def result_relative_path(row):
    return Path("cases") / row["case_id"] / row["variant"] / "result.json"


def is_solved(row):
    """Reference match or an explicitly audited semantic/tolerance exception.

    This is not an exact-equivalence count. Keep matches_truth unchanged.
    Resource failures and Unknown can never become solved through annotations.
    """
    if row.get("status") != "completed" or row.get("verdict") not in ("eq", "neq", "approx_eq"):
        return False
    if row.get("matches_truth") is True:
        return True
    audit = row.get("solve_adjudication", {})
    return (row.get("solved") is True and audit.get("accepted") is True
            and bool(audit.get("policy")) and bool(audit.get("evidence")))


def summarize(rows):
    grouped = defaultdict(list)
    suites = defaultdict(list)
    for row in rows:
        grouped[row["variant"]].append(row)
        suites[row["suite"]].append(row)

    def stats(items):
        compared = [row for row in items if row["matches_truth"] is not None]
        return {
            "records": len(items),
            "status": dict(sorted(Counter(row["status"] for row in items).items())),
            "verdict": dict(
                sorted(Counter(row["verdict"] if row["verdict"] is not None else "none" for row in items).items())
            ),
            "truth_compared": len(compared),
            "truth_matches": sum(row["matches_truth"] is True for row in compared),
            "solved": sum(is_solved(row) for row in items),
            "adjudicated_additional_solved": sum(
                is_solved(row) and row.get("matches_truth") is not True for row in items
            ),
            "total_wall_time_sec": round(sum(row["wall_time_sec"] for row in items), 6),
            "max_peak_rss_bytes": max((row["peak_rss_bytes"] for row in items), default=0),
        }

    return {
        "schema_version": 1,
        "records": len(rows),
        "cases": len({row["case_id"] for row in rows}),
        "by_variant": {name: stats(items) for name, items in sorted(grouped.items())},
        "by_suite": {name: stats(items) for name, items in sorted(suites.items())},
    }


def render_outputs(run_dir, records, tool, collection, manifest):
    ordered = sorted(records, key=lambda row: (row["case_id"], row["variant"]))
    for row in ordered:
        path = run_dir / result_relative_path(row)
        atomic_write(path, json.dumps(row, indent=2, sort_keys=True) + "\n")
    atomic_write(
        run_dir / "results.jsonl",
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in ordered),
    )
    summary = summarize(ordered)
    summary.update(
        {
            "tool": tool,
            "collection": collection,
            "manifest": str(manifest.resolve().relative_to(ROOT)),
        }
    )
    atomic_write(run_dir / "summary.json", json.dumps(summary, indent=2, sort_keys=True) + "\n")


async def run_process(command, timeout, memory_limit, env):
    start = time.monotonic()
    process = await asyncio.create_subprocess_exec(
        *command,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        env=env,
        cwd=ROOT,
        start_new_session=True,
    )
    peak = 0
    reason = None
    while process.returncode is None:
        current = rss_bytes(process.pid)
        peak = max(peak, current)
        elapsed = time.monotonic() - start
        if current > memory_limit:
            reason = "memory_limit"
        elif elapsed > timeout:
            reason = "timeout"
        if reason:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            await asyncio.sleep(1)
            if process.returncode is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            break
        await asyncio.sleep(0.1)
    stdout, stderr = await process.communicate()
    return process.returncode, time.monotonic() - start, peak, reason, stdout, stderr


async def main_async(args):
    manifest = args.manifest.resolve()
    collection = args.collection or collection_name(manifest)
    run_dir = EXPERIMENTS / args.tool / collection
    runtime_dir = RUNTIME / args.tool / collection
    for directory in (run_dir / "cases", runtime_dir / "jobs", runtime_dir / "tmp"):
        directory.mkdir(parents=True, exist_ok=True)

    records = load_existing(run_dir)
    completed = {(row["variant"], row["case_id"]) for row in records}
    cases = load_cases(manifest)
    if args.suite:
        cases = [case for case in cases if case["suite"] == args.suite]
    if args.case:
        wanted = set(args.case)
        cases = [case for case in cases if case["id"] in wanted]

    jobs = []
    for case in cases:
        case = dict(case)
        case["sqbricks_variants"] = list(variants("sqbricks", case))
        case_file = runtime_dir / "jobs" / f'{case["id"]}.json'
        atomic_write(case_file, json.dumps(case, indent=2, sort_keys=True) + "\n")
        if not all((variant, case["id"]) in completed for variant in variants(args.tool, case)):
            jobs.append((case, case_file))

    semaphore = asyncio.Semaphore(args.jobs)
    write_lock = asyncio.Lock()
    memory_limit = int(args.memory_gib * (1024**3))
    commit = commits()[args.tool]

    async def execute(case, case_file):
        nonlocal records
        async with semaphore:
            while read_mem_available() < args.reserve_memory_gib * (1024**3):
                await asyncio.sleep(5)
            command = worker_command(args.tool, case_file, runtime_dir, case["id"], args.qcec_threads)
            env = os.environ.copy()
            env.update(
                {
                    "TMPDIR": str(runtime_dir / "tmp"),
                    "OMP_NUM_THREADS": "1",
                    "OPENBLAS_NUM_THREADS": "1",
                    "MKL_NUM_THREADS": "1",
                    "NUMEXPR_NUM_THREADS": "1",
                }
            )
            code, wall, peak, stop_reason, stdout, stderr = await run_process(
                command, args.timeout, memory_limit, env
            )
            payload = None
            for line in reversed(stdout.decode(errors="replace").splitlines()):
                if line.startswith("RESULT_JSON="):
                    try:
                        payload = json.loads(line[len("RESULT_JSON=") :])
                    except json.JSONDecodeError:
                        pass
                    break
            if payload is None:
                payload = {
                    "results": [
                        {
                            "variant": variant,
                            "status": stop_reason or "error",
                            "verdict": None,
                            "message": "worker produced no normalized result",
                        }
                        for variant in variants(args.tool, case)
                    ]
                }

            new_records = []
            for result in payload["results"]:
                key = (result["variant"], case["id"])
                if key in completed:
                    continue
                case_dir = run_dir / "cases" / case["id"] / result["variant"]
                stdout_path = case_dir / "stdout.log"
                stderr_path = case_dir / "stderr.log"
                case_dir.mkdir(parents=True, exist_ok=True)
                stdout_path.write_text(portable_text(stdout.decode(errors="replace"), ROOT))
                stderr_path.write_text(portable_text(stderr.decode(errors="replace"), ROOT))
                verdict = result.get("verdict")
                row = {
                    "schema_version": 1,
                    "collection": collection,
                    "case_id": case["id"],
                    "suite": case["suite"],
                    "tool": args.tool,
                    "variant": result["variant"],
                    "tool_commit": commit,
                    "truth": case["truth"],
                    "equivalence": case["equivalence"],
                    "status": result.get("status", "error"),
                    "verdict": verdict,
                    "matches_truth": verdict == case["truth"] if verdict in ("eq", "neq") else None,
                    "wall_time_sec": round(wall, 6),
                    "peak_rss_bytes": peak,
                    "exit_code": code,
                    "left": case["left"],
                    "right": case["right"],
                    "input_pairs": case["input_pairs"],
                    "output_pairs": case["output_pairs"],
                    "stdout_path": str(stdout_path.relative_to(run_dir)),
                    "stderr_path": str(stderr_path.relative_to(run_dir)),
                }
                row.update(
                    {key: value for key, value in result.items() if key not in ("variant", "status", "verdict")}
                )
                new_records.append(row)
                completed.add(key)
            async with write_lock:
                records.extend(new_records)
                render_outputs(run_dir, records, args.tool, collection, manifest)
                print(
                    f'[{len(records)} records] {args.tool} {case["id"]} '
                    f"wall={wall:.2f}s peak={peak / 2**20:.1f}MiB",
                    flush=True,
                )

    print(
        json.dumps(
            {
                "tool": args.tool,
                "collection": collection,
                "manifest": str(manifest.relative_to(ROOT)),
                "cases": len(cases),
                "jobs": len(jobs),
                "parallel": args.jobs,
                "timeout_sec": args.timeout,
                "reserve_memory_gib": args.reserve_memory_gib,
                "memory_gib": args.memory_gib,
            },
            sort_keys=True,
        ),
        flush=True,
    )
    await asyncio.gather(*(execute(*job) for job in jobs))
    render_outputs(run_dir, records, args.tool, collection, manifest)
    print(f"complete: {len(records)} records", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--collection")
    parser.add_argument("--tool", required=True, choices=("qcec", "veriqc", "sqbricks", "irene"))
    parser.add_argument("--suite")
    parser.add_argument("--case", action="append")
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--qcec-threads", type=int, default=2)
    parser.add_argument("--timeout", type=int, default=7200)
    parser.add_argument("--reserve-memory-gib", type=float, default=20)
    parser.add_argument("--memory-gib", type=float, default=6)
    args = parser.parse_args()
    asyncio.run(main_async(args))


if __name__ == "__main__":
    main()

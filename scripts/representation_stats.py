#!/usr/bin/env python3
"""Offline, bounded XAG -> canonical ANF census and whole-corpus aggregation.

No verifier code is called. XOR uses symmetric difference, AND uses square-free
monomial products. Budgets do not establish a lower bound on final ANF size.
ANF storage models intern identical monomials AND identical complete polynomials
across roots in each snapshot. They do not model persistent-trie node sharing.
"""
import argparse
import csv
import json
import math
from pathlib import Path


class BudgetExceeded(Exception):
    pass


def analyze_snapshot(snapshot, max_terms=100_000, max_work=2_000_000,
                     max_live_entries=500_000, max_live_variable_refs=2_000_000):
    nodes, edges, roots = snapshot["nodes"], snapshot["edges"], snapshot["roots"]
    # Cache every node only within one snapshot, sharing equal polynomials.
    values, interned = [], {}
    work = live_entries = live_variables = 0

    def spend(n):
        nonlocal work
        work += n
        if work > max_work:
            raise BudgetExceeded("work_limit")

    def retain(poly):
        nonlocal live_entries, live_variables
        if len(poly) > max_terms:
            raise BudgetExceeded("intermediate_term_limit")
        poly = frozenset(poly)
        if poly in interned:
            return interned[poly]
        live_entries += len(poly)
        live_variables += sum(map(len, poly))
        if live_entries > max_live_entries or live_variables > max_live_variable_refs:
            raise BudgetExceeded("intermediate_storage_limit")
        interned[poly] = poly
        return poly

    variables = set()
    for index, row in enumerate(nodes):
        kind, a, b = row
        spend(1)
        if kind == 0:
            if a not in (0, 1):
                raise ValueError("invalid constant")
            result = {()} if a else set()
        elif kind in (1, 2):
            variable = (kind, a, b)
            variables.add(variable)
            result = {(variable,)}
        elif kind in (3, 4):
            if a < 0 or b < 0 or a + b > len(edges):
                raise ValueError("invalid edge range")
            result = set() if kind == 3 else {()}
            for child in edges[a:a+b]:
                if child < 0 or child >= index:
                    raise ValueError("graph is not topologically ordered")
                rhs = values[child]
                if kind == 3:
                    spend(len(rhs))
                    result.symmetric_difference_update(rhs)
                else:
                    spend(len(result) * len(rhs))
                    product = set()
                    for x in result:
                        for y in rhs:
                            spend(len(x) + len(y))
                            monomial = tuple(sorted(set(x).union(y)))
                            if monomial in product:
                                product.remove(monomial)
                            else:
                                product.add(monomial)
                            if len(product) > max_terms:
                                raise BudgetExceeded("intermediate_term_limit")
                    result = product
                if len(result) > max_terms:
                    raise BudgetExceeded("intermediate_term_limit")
        else:
            raise ValueError("invalid XAG node kind")
        values.append(retain(result))
    if any(r < 0 or r >= len(values) for r in roots):
        raise ValueError("invalid root")
    polynomials = {values[r] for r in roots}
    monomials = set().union(*polynomials) if polynomials else set()
    variables = {variable for monomial in monomials for variable in monomial}
    memberships = sum(map(len, polynomials))
    variable_refs = sum(map(len, monomials))
    # A comparable portable layout: all IDs/offsets u64, two u64s per
    # polynomial/monomial descriptor; each variable has a three-u64 identity.
    shared_bytes = (24 * len(variables) + 16 * len(polynomials)
                    + 16 * len(monomials) + 8 * memberships
                    + 8 * variable_refs + 8 * len(roots))
    unshared_terms = sum(len(values[r]) for r in roots)
    unshared_variable_refs = sum(sum(map(len, values[r])) for r in roots)
    unshared_bytes = (24 * len(variables) + 16 * len(roots)
                      + 16 * unshared_terms + 8 * unshared_variable_refs
                      + 8 * unshared_terms + 8 * len(roots))
    return {
        "status": "exact", "xag_nodes": len(nodes), "xag_edges": len(edges),
        "xag_packed_bytes": 24 * len(nodes) + 8 * (len(edges) + len(roots)),
        "xag_buffer_bytes": snapshot["xag_buffer_bytes"],
        "anf_unique_polynomials": len(polynomials), "anf_unique_monomials": len(monomials),
        "anf_monomial_memberships": memberships, "anf_variable_occurrences": variable_refs,
        "anf_shared_estimated_bytes": shared_bytes,
        "anf_unshared_monomials": unshared_terms,
        "anf_unshared_estimated_bytes": unshared_bytes,
    }


METRICS = ("xag_nodes", "xag_edges", "xag_packed_bytes", "xag_buffer_bytes",
           "anf_unique_polynomials", "anf_unique_monomials", "anf_monomial_memberships",
           "anf_variable_occurrences", "anf_shared_estimated_bytes",
           "anf_unshared_monomials", "anf_unshared_estimated_bytes")


def analyze_file(path, **budgets):
    counts = {"snapshots": 0, "exact": 0, "expansion_budget_exceeded": 0}
    peaks = {metric: 0 for metric in METRICS}
    reasons, header, footer, invalid = {}, None, None, None
    try:
        with open(path, encoding="utf-8") as source:
            for line in source:
                if footer is not None:
                    raise ValueError("records after completion footer")
                record = json.loads(line)
                kind = record.get("type")
                if kind == "header":
                    if header is not None or record.get("schema_version") != 1:
                        raise ValueError("invalid header")
                    header = record
                elif header is None:
                    raise ValueError("missing header")
                elif kind == "end":
                    footer = record
                elif kind == "snapshot":
                    counts["snapshots"] += 1
                    try:
                        measured = analyze_snapshot(record, **budgets)
                    except BudgetExceeded as error:
                        counts["expansion_budget_exceeded"] += 1
                        reason = str(error)
                        reasons[reason] = reasons.get(reason, 0) + 1
                        continue
                    counts["exact"] += 1
                    for metric in METRICS:
                        peaks[metric] = max(peaks[metric], measured[metric])
                elif kind != "skipped":
                    raise ValueError("unknown record type")
    except (OSError, ValueError, KeyError, TypeError, IndexError, MemoryError, RecursionError) as error:
        invalid = f"{type(error).__name__}: {error}"
    if footer and footer.get("snapshots") != counts["snapshots"]:
        invalid = "snapshot/footer count mismatch"
    complete = (invalid is None and footer is not None and footer.get("skipped") == 0
                and counts["snapshots"] > 0 and counts["expansion_budget_exceeded"] == 0)
    return {"path": str(path), "header": header, "footer": footer, "counts": counts,
            "budget_reasons": reasons, "error": invalid, "paired_complete": complete,
            # Partial maxima must never be presented as complete per-case peaks.
            "paired_observed_maxima": peaks if complete else None}


def aggregate(cases):
    complete = [c for c in cases if c["paired_complete"]]
    settings = {(c["header"].get("scope"), c["header"].get("every")) for c in complete}
    if len(settings) > 1:
        raise ValueError("cannot pool traces with different scopes/sampling intervals")
    mean = {metric: (sum(c["paired_observed_maxima"][metric] for c in complete) / len(complete)
                     if complete else None) for metric in METRICS}
    ratios = [c["paired_observed_maxima"]["anf_shared_estimated_bytes"] /
              c["paired_observed_maxima"]["xag_packed_bytes"] for c in complete
              if c["paired_observed_maxima"]["xag_packed_bytes"]]
    return {"cases": len(cases), "paired_complete_cases": len(complete),
            "incomplete_or_unobserved_cases": len(cases) - len(complete),
            "cases_with_anf_budget_exceeded": sum(c["counts"]["expansion_budget_exceeded"] > 0 for c in cases),
            "cases_with_capture_truncation": sum(bool(c["footer"] and c["footer"].get("skipped")) for c in cases),
            "cases_without_completion_footer": sum(c["footer"] is None for c in cases),
            "mean_per_case_observed_maxima": mean,
            "geomean_shared_anf_to_packed_xag_bytes": math.exp(sum(map(math.log, ratios))/len(ratios)) if ratios else None,
            "interpretation": "HPS Boolean-expression snapshots only; maxima at observed checkpoints, not verifier heap/RSS; incomplete cases excluded from paired means"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("traces", nargs="+", type=Path, help="One trace per program pair; directories are searched for *.jsonl")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--table-csv", type=Path, help="Optional NEW two-row, four-column corpus table; paired denominator remains in summary JSON")
    parser.add_argument("--max-terms", type=int, default=100_000)
    parser.add_argument("--max-work", type=int, default=2_000_000)
    parser.add_argument("--max-live-entries", type=int, default=500_000)
    parser.add_argument("--max-live-variable-refs", type=int, default=2_000_000)
    args = parser.parse_args()
    paths = sorted({p.resolve() for path in args.traces for p in
                    (path.rglob("*.jsonl") if path.is_dir() else [path])})
    if not paths:
        parser.error("no traces found")
    budgets = {name: getattr(args, name) for name in
               ("max_terms", "max_work", "max_live_entries", "max_live_variable_refs")}
    if min(budgets.values()) <= 0:
        parser.error("budgets must be positive")
    cases = [analyze_file(path, **budgets) for path in paths]
    result = {"schema_version": 1, "budgets": budgets, "summary": aggregate(cases), "cases": cases}
    with args.output.open("x", encoding="utf-8") as output:
        json.dump(result, output, indent=2)
        output.write("\n")
    if args.table_csv:
        columns = ("xag_nodes", "xag_packed_bytes", "anf_unique_monomials", "anf_shared_estimated_bytes")
        with args.table_csv.open("x", encoding="utf-8", newline="") as output:
            writer = csv.writer(output)
            writer.writerow(("XAG nodes", "XAG packed storage (bytes)", "Shared ANF monomials", "Shared ANF storage (estimated bytes)"))
            means = result["summary"]["mean_per_case_observed_maxima"]
            writer.writerow("NA" if means[c] is None else f"{means[c]:.2f}" for c in columns)
    print(json.dumps(result["summary"], indent=2))


if __name__ == "__main__":
    main()

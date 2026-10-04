import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[2] / "scripts" / "representation_stats.py"
SPEC = importlib.util.spec_from_file_location("representation_stats", SCRIPT)
representation_stats = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(representation_stats)
BudgetExceeded = representation_stats.BudgetExceeded
aggregate = representation_stats.aggregate
analyze_file = representation_stats.analyze_file
analyze_snapshot = representation_stats.analyze_snapshot


def snapshot(nodes, edges, roots):
    return {"type": "snapshot", "nodes": nodes, "edges": edges, "roots": roots,
            "xag_buffer_bytes": 24 * len(nodes) + 8 * (len(edges) + len(roots))}


class RepresentationTests(unittest.TestCase):
    def test_monomial_and_polynomial_interning(self):
        # Two separate XAG variable nodes with the same meaning, two output roots.
        s = snapshot([[2, 0, 0], [2, 0, 0]], [], [0, 1])
        result = analyze_snapshot(s)
        self.assertEqual(result["anf_unique_polynomials"], 1)
        self.assertEqual(result["anf_unique_monomials"], 1)
        self.assertEqual(result["anf_variable_occurrences"], 1)
        self.assertEqual(result["anf_shared_estimated_bytes"], 88)
        self.assertLess(result["anf_shared_estimated_bytes"], result["anf_unshared_estimated_bytes"])

    def test_boolean_idempotence_and_xor_cancellation(self):
        # x*x XOR x = 0, using deliberately unnormalized input syntax.
        s = snapshot([[2, 0, 0], [4, 0, 2], [3, 2, 2]], [0, 0, 1, 0], [2])
        result = analyze_snapshot(s)
        self.assertEqual(result["anf_unique_monomials"], 0)
        self.assertEqual(result["anf_variable_occurrences"], 0)

    def test_product_has_exact_exponential_expansion(self):
        nodes, edges, factors = [], [], []
        for i in range(8):
            a = len(nodes)
            nodes.extend([[2, 2*i, 0], [2, 2*i+1, 0], [3, len(edges), 2]])
            edges.extend([a, a+1])
            factors.append(a+2)
        nodes.append([4, len(edges), len(factors)])
        edges.extend(factors)
        s = snapshot(nodes, edges, [len(nodes)-1])
        result = analyze_snapshot(s)
        self.assertEqual(result["anf_unique_monomials"], 256)
        self.assertEqual(result["anf_variable_occurrences"], 2048)
        with self.assertRaises(BudgetExceeded):
            analyze_snapshot(s, max_terms=16)

    def test_empty_sum_and_constant_one_differ(self):
        zero = analyze_snapshot(snapshot([[0, 0, 0]], [], [0]))
        one = analyze_snapshot(snapshot([[0, 1, 0]], [], [0]))
        self.assertEqual(zero["anf_unique_monomials"], 0)
        self.assertEqual(one["anf_unique_monomials"], 1)
        self.assertEqual(one["anf_variable_occurrences"], 0)

    def test_truncation_and_budget_failures_never_enter_paired_means(self):
        with tempfile.TemporaryDirectory() as directory:
            header = {"type": "header", "schema_version": 1, "every": 1, "scope": "test"}
            s = snapshot([[2, 0, 0], [2, 1, 0], [3, 0, 2]], [0, 1], [2])
            end = {"type": "end", "snapshots": 1, "skipped": 0}
            def trace(name, records):
                path = Path(directory) / name
                path.write_text("".join(json.dumps(r) + "\n" for r in records))
                return path
            good = trace("good.jsonl", [header, s, end])
            truncated = trace("truncated.jsonl", [header, s])
            capture_skipped = trace("skipped.jsonl", [header, s, dict(end, skipped=1)])
            cases = [analyze_file(good), analyze_file(truncated), analyze_file(capture_skipped),
                     analyze_file(good, max_terms=1)]
            summary = aggregate(cases)
            self.assertEqual(summary["paired_complete_cases"], 1)
            self.assertEqual(summary["cases_with_anf_budget_exceeded"], 1)
            self.assertTrue(all(c["paired_observed_maxima"] is None for c in cases[1:]))

    def test_mixed_sampling_is_rejected(self):
        case = {"paired_complete": True, "header": {"scope": "test", "every": 1}}
        other = dict(case, header={"scope": "test", "every": 32})
        with self.assertRaises(ValueError):
            aggregate([case, other])


if __name__ == "__main__":
    unittest.main()

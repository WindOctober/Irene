#!/usr/bin/env python3
import argparse
import json


def emit(payload):
    print("RESULT_JSON=" + json.dumps(payload, sort_keys=True))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("case_file")
    parser.add_argument("--threads", type=int, default=2)
    args = parser.parse_args()
    with open(args.case_file, encoding="utf-8") as handle:
        case = json.load(handle)

    try:
        from mqt import qcec
        from mqt.qcec.pyqcec import EquivalenceCriterion

        result = qcec.verify(
            case["left_abs"],
            case["right_abs"],
            transform_dynamic_circuit=True,
            # Preserve the benchmark's given input mapping, including for dynamic circuits.
            backpropagate_output_permutation=False,
            check_partial_equivalence=case["equivalence"] == "partial",
            nthreads=args.threads,
        )
        criterion = result.equivalence
        eq = {
            EquivalenceCriterion.equivalent,
            EquivalenceCriterion.equivalent_up_to_global_phase,
            EquivalenceCriterion.equivalent_up_to_phase,
        }
        neq = {
            EquivalenceCriterion.not_equivalent,
            EquivalenceCriterion.probably_not_equivalent,
        }
        verdict = "eq" if criterion in eq else "neq" if criterion in neq else "unknown"
        emit(
            {
                "results": [
                    {
                        "variant": "dynamic",
                        "status": "completed",
                        "verdict": verdict,
                        "native_result": str(criterion),
                        "tool_time_sec": float(result.check_time + result.preprocessing_time),
                    }
                ]
            }
        )
    except Exception as exc:
        text = f"{type(exc).__name__}: {exc}"
        unsupported_markers = (
            "not supported",
            "unsupported",
            "more than one classical bit",
            "cannot import",
        )
        status = "unsupported" if any(marker in text.lower() for marker in unsupported_markers) else "error"
        emit({"results": [{"variant": "dynamic", "status": status, "verdict": None, "message": text}]})


if __name__ == "__main__":
    main()

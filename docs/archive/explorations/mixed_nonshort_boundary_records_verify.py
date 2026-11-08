#!/usr/bin/env python3
"""Verify the four published two-root boundary receipts and both fresh logs.

This is record/hash accounting, not a substitute for compiling and executing
the interval callers or for their mathematical domain and source audits.
No Lean or CI is invoked. Run from any working directory.
"""
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCES = {
    "reverse": "984f729590c1933ad7677b0d4a7392210f36f6a49f63f607b1576a4c6b69557c",
    "low_a": "448b6ad8858dcb6568a8748a41722d686e1fa525cc819cb87f7eff37a5e01edd",
    "forward": "fc5a99b57c7546df86a4f800063f417a01537f0264de9b4c349ef323e839ad27",
}
HEADERS = {
    "certified_mpfr_interval.hpp": "1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76",
    "certified_lp_proposal.hpp": "6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454",
    "mixed_nonshort_coefficients.hpp": "5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d",
}
# Prefix, source class, branch, nodes, leaves, depth, closed a interval.
CASES = [
    ("mixed_nonshort_reverse_boundary", "reverse", 1, 106134, 53068, 26, ["2/15", "17/20"]),
    ("mixed_nonshort_low_a_boundary", "low_a", 2, 74772, 37387, 23, ["2/15", "1/2"]),
    ("mixed_nonshort_forward_boundary_0", "forward", 0, 37940, 18971, 27, ["1/2", "17/20"]),
    ("mixed_nonshort_forward_boundary_1", "forward", 1, 60976, 30489, 32, ["1/2", "17/20"]),
]
FINAL = re.compile(
    r"^FINAL branch (\d+) nodes (\d+) stack (\d+) depth (\d+) unknown (\d+) seconds ([\d.]+)$",
    re.MULTILINE,
)
REASON = re.compile(r"^reason (\d+) leaves (\d+)$", re.MULTILINE)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_complete_log(path, expected):
    branch, nodes, leaves, depth = expected
    text = path.read_text()
    matches = list(FINAL.finditer(text))
    require(len(matches) == 1, f"Expected one final record: {path}")
    final = matches[0]
    require(tuple(map(int, final.groups()[:5])) == (branch, nodes, 0, depth, 0),
            f"Wrong final accounting: {path}")
    tail = text[final.end():]
    pairs = REASON.findall(tail)
    reasons = {k: int(v) for k, v in pairs}
    require(len(reasons) == len(pairs) and all(v > 0 for v in reasons.values()),
            f"Duplicate or invalid reason counter: {path}")
    require(sum(reasons.values()) == leaves and nodes == 2 * leaves - 2,
            f"Two-root forest identity failed: {path}")
    require(text.rstrip().endswith(
        "PASS: complete two-chart " +
        ("reverse boundary" if "reverse" in path.name else
         "low-a boundary" if "low_a" in path.name else "forward endpoint") +
        " domain excluded; interface audit still required."),
        f"Missing fresh full-domain PASS: {path}")
    require("INCOMPLETE" not in text and "supplied pending domain" not in text,
            f"Incomplete or checkpoint-only record: {path}")
    return reasons, text[final.start():]


def main():
    for header, expected in HEADERS.items():
        require(digest(ROOT / "explorations" / header) == expected, header + " hash changed")
    for prefix, kind, branch, nodes, leaves, depth, a_range in CASES:
        path = ROOT / "explorations" / (prefix + "_result.json")
        record = json.loads(path.read_text())
        require(record["root_count"] == 2 and record["charts"] == [1, 2], prefix + " roots")
        require(record["coordinates"] == ["a", "c", "epsilon", "l0=0", "other_weight"],
                prefix + " coordinates")
        require(record["roots"] == {
            "a": a_range, "c": ["2/15", "2"], "epsilon": ["1/32", "15"],
            "l0": ["0", "0"], "other_weight": ["0", "1"],
        }, prefix + " root domains")
        source_name = "mixed_nonshort_" + kind + "_boundary_interval_certificate.cpp"
        source = ROOT / "explorations" / source_name
        require(digest(source) == SOURCES[kind], prefix + " source hash")
        require(record["published_artifacts"][str(source.relative_to(ROOT))] == SOURCES[kind],
                prefix + " source receipt")
        for name, expected in record["published_artifacts"].items():
            artifact = (ROOT / name).resolve()
            require(artifact.is_relative_to(ROOT), "Artifact outside repository")
            require(digest(artifact) == expected, f"Artifact hash changed: {name}")
        require((record["branch"], record["nodes"], record["leaves"],
                 record["pending"], record["unresolved"], record["maximum_depth"])
                == (branch, nodes, leaves, 0, 0, depth), prefix + " original receipt")
        original, _ = read_complete_log(
            ROOT / "explorations/results" / (prefix + "_original.log"),
            (branch, nodes, leaves, depth))
        replay, replay_tail = read_complete_log(
            ROOT / "explorations/results" / (prefix + "_replay.log"),
            (branch, nodes, leaves, depth))
        require(original == replay == record["leaf_reasons"], prefix + " reason mismatch")
        independent = record["independent_replay"]
        require(independent["exit_code"] == 0 and independent["fresh_original_roots"]
                and not independent["supplied_pending_stack"], prefix + " replay provenance")
        require((independent["branch"], independent["nodes"], independent["leaves"],
                 independent["pending"], independent["unresolved"], independent["maximum_depth"])
                == (branch, nodes, leaves, 0, 0, depth), prefix + " replay receipt")
        require(independent["leaf_reasons"] == original and independent["unresolved_file_bytes"] == 0,
                prefix + " replay leaves/frontier")
        require(independent["final_output"] == replay_tail, prefix + " replay text")
        require(independent["log_sha256"] == digest(
            ROOT / "explorations/results" / (prefix + "_replay.log")), prefix + " replay hash")
        print(f"PASS {prefix}: {nodes}=2*{leaves}-2, two fresh complete logs; source and headers unchanged")
    print("ALL FOUR BOUNDARY RECORDS VERIFIED; mathematical/source audits and execution trust remain explicit")


if __name__ == "__main__":
    main()

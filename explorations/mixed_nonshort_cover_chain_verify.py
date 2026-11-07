#!/usr/bin/env python3
"""Independently verify a rooted nonshort interval-cover execution record.

This does not trust the coordinator's status, counters, or partitioning.
It checks the frozen mathematical sources, every job result, every exact
checkpoint record, and the entire rooted forest. It does not authenticate
that a computation happened: as for a serial replay record, execution of
the audited C++ program and arithmetic libraries remains a named trust
boundary. No Lean command or interval-proof computation is performed here.

Default mode also rehashes the retained executable and external MPFR
header. --archive explicitly permits their absence in a portable archive;
their recorded hashes must still agree throughout the execution record.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from decimal import Decimal
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


EXPECTED_SOURCES = {
    "mixed_nonshort_completion_interval_certificate.cpp":
        "fc15bd27e0c19700297717747fc70209ac3a2f2eacb0f677a11e3e97e056d560",
    "certified_lp_proposal.hpp":
        "6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454",
    "mixed_nonshort_coefficients.hpp":
        "5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d",
    "certified_mpfr_interval.hpp":
        "1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76",
}
FULL_PASS = "PASS: this complete quantified branch is excluded; interface audit still required."
PENDING_PASS = "PASS: supplied pending domain exhausted; not a stand-alone quantified proof."
INCOMPLETE = "INCOMPLETE: no M2 exclusion."
FINAL = re.compile(
    r"FINAL branch ([01]) nodes (\d+) stack (\d+) depth (\d+) "
    r"unknown (\d+) seconds (\d+(?:\.\d+)?)")
LEAF = re.compile(r"reason (\d+) leaves (\d+)")
HEX = re.compile(r"[0-9a-f]{64}")
INTEGER = re.compile(rb"(?:0|-[1-9][0-9]*|[1-9][0-9]*)")


class InvalidRecord(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidRecord(message)


def integer(value: object, name: str, minimum: int = 0) -> int:
    require(type(value) is int and value >= minimum, f"{name}: invalid integer")
    return value


def sha256(path: Path) -> str:
    require(path.is_file(), f"missing regular file: {path}")
    with path.open("rb") as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def digest_matches(path: Path, expected: object, name: str) -> None:
    require(type(expected) is str and HEX.fullmatch(expected) is not None,
            f"{name}: invalid SHA256 identifier")
    require(sha256(path) == expected, f"{name}: SHA256 mismatch")


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def bad_constant(value: str) -> None:
    raise InvalidRecord(f"nonfinite JSON constant: {value}")


def read_json(path: Path) -> dict:
    result = json.loads(path.read_text(), object_pairs_hook=unique_object,
                        parse_float=Decimal, parse_constant=bad_constant)
    require(type(result) is dict, f"{path}: JSON object required")
    return result


def inside(base: Path, relative: object) -> Path:
    require(type(relative) is str and bool(relative), "missing relative bundle path")
    parts = PurePosixPath(relative)
    require(not parts.is_absolute() and ".." not in parts.parts,
            f"path escapes bundle: {relative}")
    path = (base / relative).resolve()
    require(path.is_relative_to(base), f"symlink escapes bundle: {relative}")
    return path


# A canonical dyadic is n*2**e with n odd, or (0,0).  Comparison does not
# construct 2**e; MPFR's exact zero uses a huge negative exponent sentinel.
Dyadic = tuple[int, int]


def canonical(numerator: int, exponent: int) -> Dyadic:
    if numerator == 0:
        return (0, 0)
    require(numerator > 0, "negative coordinate endpoint")
    shift = (numerator & -numerator).bit_length() - 1
    result = (numerator >> shift, exponent + shift)
    require(result[0].bit_length() <= 80, "endpoint is not exactly representable at 80 bits")
    return result


def compare(a: Dyadic, b: Dyadic) -> int:
    if not a[0] or not b[0]:
        return (a[0] > b[0]) - (a[0] < b[0])
    order_a, order_b = a[0].bit_length() + a[1], b[0].bit_length() + b[1]
    if order_a != order_b:
        return (order_a > order_b) - (order_a < order_b)
    common = min(a[1], b[1])
    # Equal binary orders bound both shifts by the mantissa lengths.
    left, right = a[0] << (a[1] - common), b[0] << (b[1] - common)
    return (left > right) - (left < right)


def rounded_rational(numerator: int, denominator: int, upward: bool) -> Dyadic:
    """The exact positive MPFR 80-significand-bit outward endpoint."""
    require(numerator >= 0 and denominator > 0, "invalid root rational")
    if numerator == 0:
        return (0, 0)
    binary_order = numerator.bit_length() - denominator.bit_length()
    if binary_order >= 0:
        below = numerator < denominator << binary_order
    else:
        below = numerator << -binary_order < denominator
    if below:
        binary_order -= 1
    exponent = binary_order - 79
    if exponent >= 0:
        scaled_n, scaled_d = numerator, denominator << exponent
    else:
        scaled_n, scaled_d = numerator << -exponent, denominator
    quotient, remainder = divmod(scaled_n, scaled_d)
    if upward and remainder:
        quotient += 1
    return canonical(quotient, exponent)


def original_root(chart: int) -> tuple[tuple[Dyadic, Dyadic], ...]:
    low_margin = rounded_rational(2, 15, False)
    return (
        (low_margin, rounded_rational(17, 20, True)),
        (low_margin, rounded_rational(2, 1, True)),
        (rounded_rational(1, 32, False),
         rounded_rational(61, 4, True) if chart == 0 else rounded_rational(15, 1, True)),
        ((0, 0), (1, 0)),
        ((0, 0), (1, 0)),
    )


@dataclass(frozen=True)
class Box:
    chart: int
    branch: int
    depth: int
    bounds: tuple[tuple[Dyadic, Dyadic], ...]
    raw: bytes


def decimal_integer(token: bytes, name: str) -> int:
    require(INTEGER.fullmatch(token) is not None, f"{name}: noncanonical integer")
    return int(token)


def parse_checkpoint(path: Path, branch: int) -> list[Box]:
    raw = path.read_bytes()
    require(raw.endswith(b"\n"), f"{path}: missing final newline")
    lines = raw.splitlines(keepends=True)
    require(bool(lines), f"{path}: empty checkpoint")
    header = re.fullmatch(rb"nonshort_max_charts_v1 ([0-9]+)\n", lines[0])
    require(header is not None, f"{path}: invalid checkpoint header")
    count = decimal_integer(header[1], "checkpoint count")
    require(0 <= count <= 1_000_000 and len(lines) == 1 + 11 * count,
            f"{path}: count mismatch or trailing unparsed lines")
    boxes = []
    for ordinal in range(count):
        block = lines[1 + 11 * ordinal:1 + 11 * (ordinal + 1)]
        label = re.fullmatch(rb"([012]) ([01]) ([0-9]+)\n", block[0])
        require(label is not None, f"{path}: invalid Box label")
        chart, actual_branch, depth = map(int, label.groups())
        require(actual_branch == branch and 0 <= depth <= 85,
                f"{path}: invalid branch or depth")
        values = []
        for line in block[1:]:
            pair = re.fullmatch(rb"([^ \n]+) ([^ \n]+)\n", line)
            require(pair is not None, f"{path}: invalid endpoint line")
            numerator = decimal_integer(pair[1], "endpoint mantissa")
            exponent = decimal_integer(pair[2], "endpoint exponent")
            values.append(canonical(numerator, exponent))
        bounds = tuple((values[i], values[i + 1]) for i in range(0, 10, 2))
        for (lo, hi), (root_lo, root_hi) in zip(bounds, original_root(chart)):
            require(compare(lo, hi) <= 0, f"{path}: reversed interval")
            require(compare(root_lo, lo) <= 0 and compare(hi, root_hi) <= 0,
                    f"{path}: Box escapes its exact outward initial root")
        boxes.append(Box(chart, branch, depth, bounds, b"".join(block)))
    require(raw == lines[0] + b"".join(box.raw for box in boxes),
            f"{path}: trailing unparsed tokens")
    return boxes


def check_build(base: Path, manifest: dict, archive: bool) -> str:
    require(manifest["source_files"] == EXPECTED_SOURCES,
            "source identifiers differ from the four audited mathematical sources")
    require(manifest["source_dir"] == "sources", "unexpected source snapshot directory")
    for name, expected in EXPECTED_SOURCES.items():
        digest_matches(inside(base, "sources/" + name), expected, name)
    digest_matches(inside(base, "coordinator.py"), manifest["coordinator_sha256"], "coordinator")
    binary = manifest["binary"]
    require(binary["path"] == "certifier", "unexpected certifier filename")
    require(type(binary["sha256"]) is str and HEX.fullmatch(binary["sha256"]),
            "invalid binary identifier")
    binary_path = inside(base, binary["path"])
    if binary_path.exists():
        digest_matches(binary_path, binary["sha256"], "certifier executable")
    else:
        require(archive, "missing certifier executable; explicit --archive required")
    build = manifest["build"]
    require(type(build["returncode"]) is int and build["returncode"] == 0,
            "unsuccessful build")
    digest_matches(inside(base, build["log"]), build["log_sha256"], "build log")
    argv = build["argv"]
    require(type(argv) is list and all(type(x) is str for x in argv), "invalid build argv")
    require(len(argv) in (8, 9), "unreviewed compiler arguments")
    require(argv[1] == "-std=c++17" and argv[2] in ("-O2", "-O3"),
            "unreviewed language/optimization flags")
    source_index = 3
    if len(argv) == 9:
        require(argv[3].startswith("-I") and len(argv[3]) > 2, "invalid include argument")
        source_index = 4
    require(PurePosixPath(argv[source_index]).name == "mixed_nonshort_completion_interval_certificate.cpp",
            "build does not name the frozen caller")
    require(argv[source_index + 1] in ("-lmpfr", "-l:libmpfr.so.6") and
            argv[source_index + 2] == "-lgmp" and argv[source_index + 3] == "-o" and
            PurePosixPath(argv[source_index + 4]).name == "certifier",
            "unexpected build/link command")
    recorded_binary = PurePosixPath(argv[-1])
    require(recorded_binary.is_absolute() and ".." not in recorded_binary.parts,
            "noncanonical recorded executable path")
    recorded_source = recorded_binary.parent / "sources" / "mixed_nonshort_completion_interval_certificate.cpp"
    require(argv[source_index] == str(recorded_source),
            "build source is not the recorded frozen source snapshot")
    require((len(argv) == 9) == ("external_mpfr_header" in manifest),
            "explicit MPFR include/header provenance mismatch")
    require(type(build["compiler_version"]) is str and bool(build["compiler_version"].strip()),
            "missing compiler version record")
    if "external_mpfr_header" in manifest:
        header = manifest["external_mpfr_header"]
        require(type(header["path"]) is str and type(header["version_macro"]) is str,
                "invalid external MPFR header record")
        require(type(header["sha256"]) is str and HEX.fullmatch(header["sha256"]),
                "invalid external MPFR header digest")
        recorded_header = PurePosixPath(header["path"])
        require(recorded_header.is_absolute() and recorded_header.name == "mpfr.h" and
                ".." not in recorded_header.parts and
                argv[3] == "-I" + str(recorded_header.parent),
                "build include directory does not match the recorded MPFR header")
        header_path = Path(header["path"])
        if header_path.exists():
            digest_matches(header_path, header["sha256"], "external MPFR header")
            versions = re.findall(r'^#define\s+MPFR_VERSION_STRING\s+"([^"]+)"',
                                  header_path.read_text(), re.M)
            require(versions == [header["version_macro"]], "MPFR version macro mismatch")
        else:
            require(archive, "missing external MPFR header; explicit --archive required")
    return argv[-1]


def verify(manifest_path: Path, archive: bool = False) -> dict:
    manifest_path = manifest_path.resolve()
    base = manifest_path.parent
    manifest = read_json(manifest_path)
    require(manifest["schema"] == "mixed_nonshort_cover_chain_v1", "unknown manifest schema")
    require(manifest["status"] == "PASS" and "error" not in manifest,
            "manifest is pending or failed")
    binary_recorded_path = check_build(base, manifest, archive)
    configuration = manifest["configuration"]
    workers = integer(configuration["workers"], "workers", 1)
    require(workers <= 6, "unreviewed worker count")
    prefix = integer(configuration["prefix_nodes"], "prefix node budget", 1)
    quantum = integer(configuration["quantum_nodes"], "quantum node budget", 1)
    roots = manifest["roots"]
    require(type(roots) is dict and set(roots) == {"0", "1"} and roots["0"] != roots["1"],
            "exactly one distinct fresh root job is required for each branch")
    require(type(manifest["jobs"]) is list and bool(manifest["jobs"]), "missing jobs")
    jobs = {}
    incoming = {}
    frontiers = {}
    for job in manifest["jobs"]:
        require(type(job) is dict, "invalid job description")
        identifier = job["id"]
        require(type(identifier) is str and re.fullmatch(r"job[0-9]{8,}", identifier), "invalid job id")
        require(identifier not in jobs, f"duplicate job id: {identifier}")
        jobs[identifier] = job
        branch = integer(job["branch"], f"{identifier} branch")
        require(branch in (0, 1), f"{identifier}: invalid branch")
        is_root = roots[str(branch)] == identifier
        require((job["parent"] is None) == is_root, f"{identifier}: orphan or false root")
        require(job["directory"] == "jobs/" + identifier, f"{identifier}: reused job directory")
        directory = inside(base, job["directory"])
        require(read_json(directory / "job.json") == job, f"{identifier}: manifest/job record mismatch")
        root_count = integer(job["root_count"], f"{identifier} root count", 1)
        require(root_count == (3 if is_root else 1), f"{identifier}: wrong input root count")
        budget = integer(job["budget"], f"{identifier} budget", 1)
        require(budget == (prefix if is_root else quantum), f"{identifier}: inconsistent budget")
        require(job["binary_sha256"] == manifest["binary"]["sha256"], f"{identifier}: binary mismatch")
        if is_root:
            require(job["input"] is None and job["input_sha256"] is None and
                    job["parent_frontier_index"] is None, f"{identifier}: fresh root has a supplied stack")
            incoming[identifier] = None
        else:
            require(type(job["parent"]) is str, f"{identifier}: missing parent id")
            integer(job["parent_frontier_index"], f"{identifier} parent ordinal")
            require(job["input"] == job["directory"] + "/input.txt", f"{identifier}: wrong input path")
            input_path = inside(base, job["input"])
            digest_matches(input_path, job["input_sha256"], identifier + " input")
            input_boxes = parse_checkpoint(input_path, branch)
            require(len(input_boxes) == 1, f"{identifier}: child must receive one exact parent record")
            incoming[identifier] = input_boxes[0]
        argv = job["argv"]
        require(type(argv) is list and all(type(x) is str for x in argv), f"{identifier}: invalid argv")
        require(argv[:3] == [binary_recorded_path, str(budget), str(branch)] and
                len(argv) == (3 if is_root else 4), f"{identifier}: incorrect caller invocation")
        if not is_root:
            recorded_bundle = str(PurePosixPath(binary_recorded_path).parent)
            require(argv[3] == recorded_bundle + "/" + job["input"], f"{identifier}: input argv mismatch")
        require(job["log"] == job["directory"] + "/stdout.log", f"{identifier}: wrong log path")
        log_path = inside(base, job["log"])
        digest_matches(log_path, job["log_sha256"], identifier + " log")
        lines = log_path.read_text().splitlines()
        finals = [FINAL.fullmatch(line) for line in lines if line.startswith("FINAL")]
        require(len(finals) == 1 and finals[0] is not None, f"{identifier}: missing/duplicate/invalid FINAL")
        actual_branch, nodes, frontier, depth, unknown = map(int, finals[0].groups()[:5])
        seconds = Decimal(finals[0][6])
        require(actual_branch == branch and 1 <= nodes <= budget and unknown == 0 and depth <= 85,
                f"{identifier}: invalid FINAL counts or unresolved box")
        for key, value in (("nodes", nodes), ("frontier", frontier), ("depth", depth), ("unknown", unknown)):
            require(type(job[key]) is int and job[key] == value, f"{identifier}: false {key} summary")
        require(Decimal(str(job["seconds"])) == seconds, f"{identifier}: time summary differs from log")
        reasons = {}
        for line in lines:
            if not line.startswith("reason"):
                continue
            match = LEAF.fullmatch(line)
            require(match is not None, f"{identifier}: malformed leaf counter")
            reason, count = map(int, match.groups())
            require(1 <= reason < 64 and count > 0 and reason not in reasons,
                    f"{identifier}: duplicate or invalid leaf counter")
            reasons[reason] = count
        leaves = sum(reasons.values())
        require(type(job["leaves"]) is int and job["leaves"] == leaves, f"{identifier}: false leaf total")
        require(job["leaf_reasons"] == {str(k): v for k, v in reasons.items()},
                f"{identifier}: false reason-counter summary")
        require(nodes == 2 * leaves + frontier - root_count, f"{identifier}: local forest conservation failed")
        unresolved = directory / f"mixed_nonshort_completion_unresolved_{branch}.txt"
        require(unresolved.is_file() and unresolved.read_bytes() == b"", f"{identifier}: unresolved/error file")
        pass_lines = [line for line in lines if line.startswith("PASS:")]
        nonempty_lines = [line for line in lines if line]
        require(type(job["returncode"]) is int, f"{identifier}: invalid return code")
        require(type(job["children"]) is list and all(type(x) is str for x in job["children"]),
                f"{identifier}: invalid child list")
        if frontier == 0:
            expected = FULL_PASS if is_root else PENDING_PASS
            require(job["returncode"] == 0 and job["status"] == "complete" and
                    pass_lines == [expected] and nonempty_lines[-1] == expected and
                    INCOMPLETE not in lines, f"{identifier}: invalid complete result")
            require(job["checkpoint"] is None and job["checkpoint_sha256"] is None and
                    not job["children"], f"{identifier}: complete job has a residual frontier")
            require(not (directory / f"mixed_nonshort_completion_pending_{branch}.txt").exists(),
                    f"{identifier}: stale checkpoint for complete job")
            frontiers[identifier] = []
        else:
            require(job["returncode"] == 1 and job["status"] == "split" and not pass_lines and
                    lines.count(INCOMPLETE) == 1 and nonempty_lines[-1] == INCOMPLETE,
                    f"{identifier}: invalid prefix result")
            require(job["checkpoint"] == job["directory"] +
                    f"/mixed_nonshort_completion_pending_{branch}.txt", f"{identifier}: wrong checkpoint path")
            checkpoint_path = inside(base, job["checkpoint"])
            digest_matches(checkpoint_path, job["checkpoint_sha256"], identifier + " checkpoint")
            boxes = parse_checkpoint(checkpoint_path, branch)
            require(len(boxes) == frontier == len(job["children"]), f"{identifier}: incomplete frontier assignment")
            require(all(box.depth <= depth + 1 for box in boxes), f"{identifier}: impossible pending depth")
            frontiers[identifier] = boxes
        if not is_root:
            require(depth >= incoming[identifier].depth, f"{identifier}: processed depth precedes its input")
            parent_box = incoming[identifier]
            for box in frontiers[identifier]:
                require(box.chart == parent_box.chart and box.depth > parent_box.depth,
                        f"{identifier}: frontier does not descend from its input box")
                require(all(compare(parent_lo, lo) <= 0 and compare(hi, parent_hi) <= 0
                            for (lo, hi), (parent_lo, parent_hi)
                            in zip(box.bounds, parent_box.bounds)),
                        f"{identifier}: frontier escapes its input box")

    require(all(root in jobs for root in roots.values()), "missing fresh root job")
    # Check every edge independently in both directions, including record
    # ordinals and exact multiplicities. No deduplication is permitted.
    for identifier, job in jobs.items():
        expected_records = frontiers[identifier]
        assigned_records = []
        for ordinal, child_id in enumerate(job["children"]):
            require(child_id in jobs, f"{identifier}: missing child {child_id}")
            child = jobs[child_id]
            require(child["parent"] == identifier and child["parent_frontier_index"] == ordinal and
                    child["branch"] == job["branch"], f"{identifier}: incorrect reciprocal child edge")
            box = incoming[child_id]
            require(box is not None and box.raw == expected_records[ordinal].raw,
                    f"{identifier}: changed or omitted frontier record {ordinal}")
            require(inside(base, child["input"]).read_bytes() ==
                    b"nonshort_max_charts_v1 1\n" + expected_records[ordinal].raw,
                    f"{identifier}: child input is not the verbatim parent record")
            assigned_records.append(box.raw)
        require(Counter(assigned_records) == Counter(box.raw for box in expected_records),
                f"{identifier}: frontier multiset mismatch")
        if job["parent"] is not None:
            require(job["parent"] in jobs, f"{identifier}: nonexistent parent")
            parent = jobs[job["parent"]]
            ordinal = job["parent_frontier_index"]
            require(ordinal < len(parent["children"]) and parent["children"][ordinal] == identifier,
                    f"{identifier}: unreferenced child job")
    totals = {}
    visited = set()
    for branch in (0, 1):
        pending = [roots[str(branch)]]
        members = []
        while pending:
            identifier = pending.pop()
            require(identifier not in visited, "cycle or multiply referenced job")
            visited.add(identifier)
            job = jobs[identifier]
            require(job["branch"] == branch, "cross-branch graph edge")
            members.append(job)
            pending.extend(job["children"])
        nodes = sum(job["nodes"] for job in members)
        leaves = sum(job["leaves"] for job in members)
        require(nodes == 2 * leaves - 3, f"branch {branch}: aggregate three-root conservation failed")
        require(sum(job["frontier"] for job in members) == len(members) - 1,
                f"branch {branch}: unmatched frontier records remain")
        totals[str(branch)] = {"nodes": nodes, "leaves": leaves, "jobs": len(members),
                               "depth": max(job["depth"] for job in members),
                               "unknown": 0, "frontier": 0}
    require(visited == set(jobs), "orphan or unreferenced jobs remain")
    require(manifest["totals"] == totals, "manifest aggregate totals differ from independent totals")
    return totals


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--archive", action="store_true",
                        help="explicitly permit absent executable/external MPFR header; retain their provenance hashes")
    args = parser.parse_args()
    try:
        totals = verify(args.manifest, archive=args.archive)
    except (InvalidRecord, OSError, KeyError, TypeError, json.JSONDecodeError, ValueError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    for branch, summary in sorted(totals.items()):
        print("PASS branch", branch, json.dumps(summary, sort_keys=True))
    if args.archive:
        print("PASS: rooted source/log archive verified; absent execution dependencies rely on recorded provenance.")
    else:
        print("PASS: rooted complete cover chain verified, including retained execution dependencies.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

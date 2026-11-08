#!/usr/bin/env python3
"""Replay the frozen nonshort certificate as a recorded exact cover chain.

This coordinator never bisects, contracts, or evaluates a mathematical box.
It copies each exact pending Box record to exactly one child invocation of
the unchanged audited certifier.  The independent offline verifier must
accept the completed manifest before this chain is used as a proof record.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
from collections import deque
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


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
FINAL = re.compile(r"^FINAL branch (\d+) nodes (\d+) stack (\d+) depth (\d+) unknown (\d+) seconds (\d+(?:\.\d+)?)$", re.M)
LEAF = re.compile(r"^reason (\d+) leaves (\d+)$", re.M)
INTEGER = re.compile(rb"-?\d+\Z")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomically_write_json(path: Path, value: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")
    temporary.replace(path)


def parse_checkpoint(path: Path, branch: int) -> list[bytes]:
    """Validate exact dyadic syntax/order and preserve all 11-line records."""
    raw = path.read_bytes()
    if not raw.endswith(b"\n"):
        raise ValueError("checkpoint lacks its final newline")
    lines = raw.splitlines(keepends=True)
    header = lines[0].split() if lines else []
    if len(header) != 2 or header[0] != b"nonshort_max_charts_v1":
        raise ValueError("invalid checkpoint header")
    count = int(header[1])
    if count < 0 or count > 1_000_000 or len(lines) != 1 + 11 * count:
        raise ValueError("checkpoint count/record length mismatch")
    records = []
    for index in range(count):
        block = lines[1 + 11 * index: 1 + 11 * (index + 1)]
        chart, actual_branch, depth = map(int, block[0].split())
        if chart not in (0, 1, 2) or actual_branch != branch or not 0 <= depth <= 85:
            raise ValueError("invalid checkpoint Box label")
        points = []
        for line in block[1:]:
            pair = line.split()
            if len(pair) != 2 or any(INTEGER.fullmatch(x) is None for x in pair):
                raise ValueError("invalid exact dyadic endpoint")
            numerator, exponent = map(int, pair)
            if numerator != 0 and abs(exponent) > 10_000:
                raise ValueError("unexpected endpoint exponent")
            # MPFR serializes zero with a very large negative sentinel
            # exponent. Its exact value is zero without exponentiation.
            points.append(Fraction(0) if numerator == 0 else
                          Fraction(numerator) * Fraction(2) ** exponent)
        if any(points[i] > points[i + 1] for i in range(0, 10, 2)):
            raise ValueError("reversed checkpoint interval")
        records.append(b"".join(block))
    if raw != lines[0] + b"".join(records):
        raise ValueError("checkpoint record preservation failed")
    return records


def check_sources(source_dir: Path) -> dict[str, str]:
    actual = {name: digest(source_dir / name) for name in EXPECTED_SOURCES}
    if actual != EXPECTED_SOURCES:
        raise ValueError("published source differs from its audited frozen hash")
    return actual


def run_job(output: Path, binary: Path, binary_hash: str,
            description: dict) -> tuple[dict, list[bytes]]:
    folder = output / description["directory"]
    folder.mkdir()
    record = description["record"]
    job = {key: value for key, value in description.items() if key != "record"}
    if record is None:
        job["input"] = None
        job["input_sha256"] = None
    else:
        input_path = folder / "input.txt"
        input_path.write_bytes(b"nonshort_max_charts_v1 1\n" + record)
        if parse_checkpoint(input_path, job["branch"]) != [record]:
            raise ValueError("child input is not the exact assigned parent record")
        job["input"] = str(input_path.relative_to(output))
        job["input_sha256"] = digest(input_path)
    argv = [str(binary), str(job["budget"]), str(job["branch"])]
    if record is not None:
        argv.append(str(output / job["input"]))
    if digest(binary) != binary_hash:
        raise ValueError("certifier executable changed before a job")
    log = folder / "stdout.log"
    with log.open("wb") as stream:
        completed = subprocess.run(argv, cwd=folder, stdout=stream, stderr=subprocess.STDOUT)
    if digest(binary) != binary_hash:
        raise ValueError("certifier executable changed during a job")
    job.update(argv=argv, returncode=completed.returncode,
               log=str(log.relative_to(output)), log_sha256=digest(log),
               binary_sha256=binary_hash)
    atomically_write_json(folder / "job.json", job)
    text = log.read_text()
    finals = FINAL.findall(text)
    if len(finals) != 1:
        raise ValueError(f"{job['id']}: missing or duplicate FINAL record")
    branch, nodes, frontier, depth, unknown = map(int, finals[0][:5])
    if branch != job["branch"] or unknown != 0 or nodes > job["budget"]:
        raise ValueError(f"{job['id']}: invalid branch/count or unresolved box")
    leaf_rows = [(int(reason), int(count)) for reason, count in LEAF.findall(text)]
    if len({reason for reason, _ in leaf_rows}) != len(leaf_rows):
        raise ValueError(f"{job['id']}: duplicate leaf counter")
    if any(not 1 <= reason < 64 or count <= 0 for reason, count in leaf_rows):
        raise ValueError(f"{job['id']}: invalid leaf counter")
    leaves = sum(count for _, count in leaf_rows)
    if nodes != 2 * leaves + frontier - job["root_count"]:
        raise ValueError(f"{job['id']}: local tree conservation failed")
    unresolved = folder / f"mixed_nonshort_completion_unresolved_{branch}.txt"
    if not unresolved.exists() or unresolved.stat().st_size != 0:
        raise ValueError(f"{job['id']}: unresolved file is absent or nonempty")
    checkpoint = folder / f"mixed_nonshort_completion_pending_{branch}.txt"
    pass_lines = [line for line in text.splitlines() if line.startswith("PASS:")]
    if completed.returncode == 0:
        expected = FULL_PASS if record is None else PENDING_PASS
        if frontier != 0 or checkpoint.exists() or pass_lines != [expected] or INCOMPLETE in text:
            raise ValueError(f"{job['id']}: invalid complete-job result")
        pending = []
        status = "complete"
    elif completed.returncode == 1:
        if frontier <= 0 or text.splitlines().count(INCOMPLETE) != 1 or pass_lines:
            raise ValueError(f"{job['id']}: invalid incomplete-prefix result")
        pending = parse_checkpoint(checkpoint, branch)
        if len(pending) != frontier:
            raise ValueError(f"{job['id']}: frontier count differs from checkpoint")
        status = "split"
    else:
        raise ValueError(f"{job['id']}: unexpected process exit {completed.returncode}")
    job.update(nodes=nodes, leaves=leaves, frontier=frontier, unknown=unknown,
               depth=depth, seconds=float(finals[0][5]), status=status,
               checkpoint=str(checkpoint.relative_to(output)) if pending else None,
               checkpoint_sha256=digest(checkpoint) if pending else None,
               children=[], leaf_reasons={str(k): v for k, v in leaf_rows})
    atomically_write_json(folder / "job.json", job)
    return job, pending


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--mpfr-include", type=Path)
    parser.add_argument("--mpfr-link", default="-lmpfr")
    parser.add_argument("--cxx", default="g++")
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument("--prefix-nodes", type=int, default=2000)
    parser.add_argument("--quantum-nodes", type=int, default=5000)
    args = parser.parse_args()
    if not 1 <= args.workers <= 6 or min(args.prefix_nodes, args.quantum_nodes) <= 0:
        parser.error("use one to six workers and positive node budgets")
    output, original_source_dir = args.output.resolve(), args.source_dir.resolve()
    output.mkdir(exist_ok=False)
    (output / "jobs").mkdir()
    sources = check_sources(original_source_dir)
    source_dir = output / "sources"
    source_dir.mkdir()
    for name in sources:
        (source_dir / name).write_bytes((original_source_dir / name).read_bytes())
    check_sources(source_dir)
    (output / "coordinator.py").write_bytes(Path(__file__).resolve().read_bytes())
    binary = output / "certifier"
    command = [args.cxx, "-std=c++17", "-O2"]
    if args.mpfr_include:
        command.append("-I" + str(args.mpfr_include.resolve()))
    command += [str(source_dir / "mixed_nonshort_completion_interval_certificate.cpp"),
                args.mpfr_link, "-lgmp", "-o", str(binary)]
    build_log = output / "build.log"
    with build_log.open("wb") as stream:
        built = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    if built.returncode:
        raise RuntimeError("frozen caller build failed; see build.log")
    check_sources(source_dir)
    binary_hash = digest(binary)
    manifest = {
        "schema": "mixed_nonshort_cover_chain_v1", "status": "RUNNING",
        "source_files": sources, "source_dir": "sources",
        "original_source_dir": str(original_source_dir),
        "binary": {"path": "certifier", "sha256": binary_hash},
        "build": {"argv": command, "returncode": built.returncode,
                  "log": "build.log", "log_sha256": digest(build_log),
                  "compiler_version": subprocess.check_output([args.cxx, "--version"], text=True)},
        "configuration": {"workers": args.workers, "prefix_nodes": args.prefix_nodes,
                          "quantum_nodes": args.quantum_nodes},
        "roots": {}, "jobs": [], "totals": {},
        "coordinator_sha256": digest(output / "coordinator.py"),
    }
    if args.mpfr_include:
        header = args.mpfr_include.resolve() / "mpfr.h"
        versions = re.findall(r'^#define\s+MPFR_VERSION_STRING\s+"([^"]+)"',
                              header.read_text(), re.M)
        manifest["external_mpfr_header"] = {
            "path": str(header), "sha256": digest(header),
            "version_macro": versions[0] if len(versions) == 1 else None}
    manifest_path = output / "manifest.json"
    queue = deque()
    next_id = 0

    def description(branch: int, parent: str | None, ordinal: int | None,
                    record: bytes | None) -> dict:
        nonlocal next_id
        identifier = f"job{next_id:08d}"
        next_id += 1
        return {"id": identifier, "directory": "jobs/" + identifier,
                "branch": branch, "parent": parent, "parent_frontier_index": ordinal,
                "root_count": 3 if parent is None else 1,
                "budget": args.prefix_nodes if parent is None else args.quantum_nodes,
                "record": record}

    for branch in (0, 1):
        item = description(branch, None, None, None)
        manifest["roots"][str(branch)] = item["id"]
        queue.append(item)
    atomically_write_json(manifest_path, manifest)
    started = time.monotonic()
    try:
        with cf.ThreadPoolExecutor(max_workers=args.workers) as pool:
            active = {}
            while queue or active:
                while queue and len(active) < args.workers:
                    item = queue.popleft()
                    future = pool.submit(run_job, output, binary, binary_hash, item)
                    active[future] = item["id"]
                done, _ = cf.wait(active, return_when=cf.FIRST_COMPLETED)
                for future in done:
                    del active[future]
                    job, pending = future.result()
                    # Every pending record gets its own child, including equal
                    # records; there is no hash deduplication or offline split.
                    for ordinal, record in enumerate(pending):
                        child = description(job["branch"], job["id"], ordinal, record)
                        job["children"].append(child["id"])
                        queue.append(child)
                    manifest["jobs"].append(job)
                    atomically_write_json(output / job["directory"] / "job.json", job)
                    atomically_write_json(manifest_path, manifest)
                    totals = {b: sum(j["nodes"] for j in manifest["jobs"] if j["branch"] == b)
                              for b in (0, 1)}
                    print(f"CHAIN jobs {len(manifest['jobs'])} queued {len(queue)} active {len(active)} "
                          f"nodes0 {totals[0]} nodes1 {totals[1]} seconds {time.monotonic()-started:.2f}", flush=True)
        check_sources(source_dir)
        if digest(binary) != binary_hash:
            raise ValueError("certifier executable changed during replay")
        for branch in (0, 1):
            jobs = [j for j in manifest["jobs"] if j["branch"] == branch]
            nodes = sum(j["nodes"] for j in jobs)
            leaves = sum(j["leaves"] for j in jobs)
            if nodes != 2 * leaves - 3:
                raise ValueError("completed three-root conservation failed")
            manifest["totals"][str(branch)] = {
                "nodes": nodes, "leaves": leaves, "jobs": len(jobs),
                "depth": max(j["depth"] for j in jobs), "unknown": 0, "frontier": 0}
        manifest["status"] = "PASS"
        manifest["elapsed_seconds"] = time.monotonic() - started
        atomically_write_json(manifest_path, manifest)
        print("PASS: recorded cover chain complete; independent manifest verification required.", flush=True)
    except BaseException as error:
        manifest["status"] = "FAILED"
        manifest["error"] = f"{type(error).__name__}: {error}"
        atomically_write_json(manifest_path, manifest)
        raise


if __name__ == "__main__":
    main()

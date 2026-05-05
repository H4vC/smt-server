#!/usr/bin/env python3
"""Run qfbvsmtrs over an SMT-LIB QF_BV corpus with resumable/incremental reports.

Full first pass:
  cargo build --release -p qfbvsmtrs
  python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
    --exe target/release/qfbvsmtrs.exe --budget-ms 3000 --timeout 30 --workers 12 \
    --report target/smtlib/qfbvsmtrs_corpus_report.jsonl

Incremental re-run that skips previously known-good (`kind == ok`) files and only
queues non-conclusive/problem files from a baseline report:
  python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
    --baseline-report target/smtlib/qfbvsmtrs_corpus_report.jsonl \
    --report target/smtlib/qfbvsmtrs_corpus_rerun.jsonl \
    --budget-ms 30000 --timeout 120 --workers 8

The output report is append-only. If interrupted, re-run the same command: paths
already present in the output report are skipped, so interrupted jobs resume.
"""

from __future__ import annotations

import argparse
import collections
import concurrent.futures
import json
import os
from pathlib import Path
import re
import subprocess
import time
from typing import Iterable

STATUS_RE = re.compile(r"\(set-info\s+:status\s+(sat|unsat|unknown)\)")
ALL_KINDS = {"ok", "unknown", "timeout", "error", "wrong", "weird"}


def expected_status(path: Path) -> str:
    # Stream instead of read_text(): a few SMT-LIB files are huge, while :status
    # is conventionally near the top.
    with path.open(encoding="utf-8", errors="ignore") as file:
        for line in file:
            match = STATUS_RE.search(line)
            if match:
                return match.group(1)
    return "none"


def relpath(root: Path, path: Path) -> str:
    # Keep the historical JSONL format on Windows while still being deterministic.
    return str(path.relative_to(root))


def parse_kind_set(text: str | None) -> set[str] | None:
    if text is None:
        return None
    values = {item.strip() for item in text.split(",") if item.strip()}
    unknown = values - ALL_KINDS
    if unknown:
        raise SystemExit(f"unknown result kind(s): {', '.join(sorted(unknown))}")
    return values


def iter_report_records(path: Path) -> Iterable[dict]:
    if not path.exists():
        return
    with path.open(encoding="utf-8") as file:
        for line in file:
            if line.strip():
                yield json.loads(line)


def load_latest_by_path(reports: list[Path]) -> dict[str, dict]:
    latest: dict[str, dict] = {}
    for report in reports:
        for record in iter_report_records(report):
            latest[record["path"]] = record
    return latest


def run_one(
    root: Path,
    exe: str,
    budget_ms: int,
    timeout: float,
    sat_backend: str | None,
    path: Path,
) -> dict:
    expected = expected_status(path)
    env = os.environ.copy()
    if budget_ms:
        env["QFBVSMTRS_BUDGET_MS"] = str(budget_ms)
    if sat_backend:
        env["QFBVSMTRS_SAT_BACKEND"] = sat_backend
    start = time.time()
    try:
        proc = subprocess.run(
            [exe, str(path)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            env=env,
        )
        first = (proc.stdout.strip().splitlines() or [""])[0]
        err = (proc.stderr.strip().splitlines() or [""])[0]
        if proc.returncode != 0:
            kind, result, detail = "error", "error", err
        elif first in ("sat", "unsat", "unknown"):
            result = detail = first
            if expected in ("sat", "unsat") and first != expected:
                kind = "unknown" if first == "unknown" else "wrong"
            else:
                kind = "ok"
        else:
            kind, result, detail = "weird", first, first
    except subprocess.TimeoutExpired:
        kind, result, detail = "timeout", "timeout", "timeout"
    return {
        "path": relpath(root, path),
        "expected": expected,
        "result": result,
        "kind": kind,
        "elapsed": time.time() - start,
        "bytes": path.stat().st_size,
        "detail": detail,
    }


def summarize_records(records: Iterable[dict]) -> dict:
    counts: collections.Counter[str] = collections.Counter()
    expected: collections.Counter[str] = collections.Counter()
    examples: dict[str, list[dict]] = collections.defaultdict(list)
    total = 0
    for record in records:
        total += 1
        counts[record["kind"]] += 1
        expected[record.get("expected", "none")] += 1
        bucket = examples[record["kind"]]
        if len(bucket) < 10:
            bucket.append(record)
    return {
        "records": total,
        "counts": dict(counts),
        "expected": dict(expected),
        "examples": dict(examples),
    }


def write_summary(
    path: Path,
    report: Path,
    baseline_reports: list[Path],
    summary_mode: str,
    queued: int,
    skipped: collections.Counter[str],
) -> None:
    if summary_mode == "merged":
        latest = load_latest_by_path([*baseline_reports, report])
        summary = summarize_records(latest.values())
        summary["mode"] = "merged-latest-by-path"
        summary["baseline_reports"] = [str(path) for path in baseline_reports]
    else:
        summary = summarize_records(iter_report_records(report))
        summary["mode"] = "report-only"
        summary["baseline_reports"] = []
    summary.update(
        {
            "report": str(report),
            "queued_this_run": queued,
            "skipped_this_run": dict(skipped),
        }
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(summary, indent=2), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--exe", default="target/release/qfbvsmtrs.exe")
    parser.add_argument("--budget-ms", type=int, default=3000)
    parser.add_argument("--timeout", type=float, default=12.0)
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--sat-backend", choices=["splr", "varisat", "dpll"])
    parser.add_argument(
        "--report",
        type=Path,
        default=Path("target/smtlib/qfbvsmtrs_corpus_report.jsonl"),
        help="append-only output report; existing paths are skipped for resume",
    )
    parser.add_argument(
        "--baseline-report",
        type=Path,
        action="append",
        default=[],
        help="previous report used for incremental selection; can be repeated",
    )
    parser.add_argument(
        "--skip-kinds",
        default="ok",
        help="comma-separated baseline kinds to skip, default: ok",
    )
    parser.add_argument(
        "--rerun-kinds",
        help="comma-separated baseline kinds to run exclusively, e.g. unknown,timeout,error,wrong",
    )
    parser.add_argument(
        "--path-contains",
        action="append",
        default=[],
        help="only queue paths containing this substring; can be repeated",
    )
    parser.add_argument(
        "--path-regex",
        help="only queue paths matching this regular expression",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="queue at most this many files after filtering (useful for sampled increments)",
    )
    parser.add_argument("--list-only", action="store_true", help="print selection summary and exit")
    parser.add_argument(
        "--summary",
        type=Path,
        help="write JSON summary; default is <report stem>_summary.json",
    )
    parser.add_argument(
        "--summary-mode",
        choices=["report", "merged"],
        default="merged",
        help="summary source: output report only, or latest records from baseline(s)+output",
    )
    args = parser.parse_args()

    skip_kinds = parse_kind_set(args.skip_kinds) or set()
    rerun_kinds = parse_kind_set(args.rerun_kinds)
    path_regex = re.compile(args.path_regex) if args.path_regex else None

    root = args.root.resolve()
    all_files = sorted(root.rglob("*.smt2"))
    output_seen = {record["path"] for record in iter_report_records(args.report)}
    baseline = load_latest_by_path(args.baseline_report)

    queued_files: list[Path] = []
    skipped: collections.Counter[str] = collections.Counter()
    for path in all_files:
        rel = relpath(root, path)
        if rel in output_seen:
            skipped["already-in-output-report"] += 1
            continue
        if args.path_contains and not any(text in rel for text in args.path_contains):
            skipped["path-filter"] += 1
            continue
        if path_regex and not path_regex.search(rel):
            skipped["path-filter"] += 1
            continue
        base = baseline.get(rel)
        if base is not None:
            kind = base["kind"]
            if rerun_kinds is not None and kind not in rerun_kinds:
                skipped[f"baseline-kind-{kind}"] += 1
                continue
            if rerun_kinds is None and kind in skip_kinds:
                skipped[f"baseline-kind-{kind}"] += 1
                continue
        elif rerun_kinds is not None:
            skipped["missing-from-baseline"] += 1
            continue
        queued_files.append(path)

    if args.limit is not None:
        skipped["over-limit"] += max(0, len(queued_files) - args.limit)
        queued_files = queued_files[: args.limit]

    print(
        "selection",
        json.dumps(
            {
                "total_files": len(all_files),
                "queued": len(queued_files),
                "skipped": dict(skipped),
                "baseline_reports": [str(path) for path in args.baseline_report],
                "output_report": str(args.report),
            },
            sort_keys=True,
        ),
        flush=True,
    )
    if args.list_only:
        return 0

    counts: collections.Counter[str] = collections.Counter()
    started = time.time()
    args.report.parent.mkdir(parents=True, exist_ok=True)
    with args.report.open("a", encoding="utf-8") as report:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = [
                pool.submit(
                    run_one,
                    root,
                    args.exe,
                    args.budget_ms,
                    args.timeout,
                    args.sat_backend,
                    path,
                )
                for path in queued_files
            ]
            for done, future in enumerate(concurrent.futures.as_completed(futures), start=1):
                record = future.result()
                counts[record["kind"]] += 1
                report.write(json.dumps(record) + "\n")
                report.flush()
                if done % 500 == 0 or record["kind"] not in ("ok",):
                    print(
                        done,
                        "/",
                        len(queued_files),
                        dict(counts),
                        "last",
                        record["kind"],
                        record["expected"],
                        record["result"],
                        f"{record['elapsed']:.2f}s",
                        record["path"][:100],
                        "elapsed",
                        f"{time.time() - started:.1f}s",
                        flush=True,
                    )
    print("done", dict(counts), "elapsed", time.time() - started)

    summary = args.summary
    if summary is None:
        summary = args.report.with_name(args.report.stem + "_summary.json")
    write_summary(
        summary,
        args.report,
        args.baseline_report,
        args.summary_mode,
        len(queued_files),
        skipped,
    )
    print("summary", summary, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

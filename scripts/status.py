#!/usr/bin/env python3
"""Render a one-page status dashboard for the repo.

Combines the output of [scripts/build.py], [scripts/audit_assumptions.py],
and [scripts/check_cleanliness.py] into a single Markdown file
(by default [STATUS.md] at the repo root).  Useful as a relay snapshot
showing, for any moment in time:

  * which sandbox files compile, and how long each takes,
  * which strict-inequality theorems are axiom-free vs FunExt-tainted,
  * which contender candidates' definitions pass the don't-be-lazy
    cleanliness check.

Usage:
    python scripts/status.py                  # write STATUS.md
    python scripts/status.py --out FILE       # to a different file
    python scripts/status.py --stdout         # print to stdout instead
    python scripts/status.py --no-cleanliness # skip the cleanliness pass

This is a *thin orchestrator*.  The three underlying scripts do the
real work and own their respective configuration; this one only stitches
their outputs together and adds a few file-level metrics (line counts,
recent git commit, etc.).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from datetime import datetime
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCRIPTS = REPO / "scripts"


def run_build(verbose: bool = False) -> tuple[bool, str, dict[str, float]]:
    """Run scripts/build.py.  Return (ok, stdout, per-file timing dict)."""
    r = subprocess.run(
        [sys.executable, str(SCRIPTS / "build.py")],
        cwd=REPO, capture_output=True, text=True,
    )
    out = r.stdout + r.stderr
    timings: dict[str, float] = {}
    for ln in out.splitlines():
        # "  build sandbox.Brouwer                       ...    1.13s"
        m = re.match(r"\s*build\s+(\S+)\s+\.\.\.\s+([\d.]+)s", ln)
        if m:
            timings[m.group(1)] = float(m.group(2))
        # "  ok    Contender                                  (.vo up to date)"
        m = re.match(r"\s*ok\s+(\S+)\s+\(.vo up to date\)", ln)
        if m:
            timings.setdefault(m.group(1), 0.0)
    return r.returncode == 0, out, timings


def run_audit() -> tuple[bool, list[dict]]:
    """Run scripts/audit_assumptions.py with --json into a temp file.
    Return (ok, parsed-json-list)."""
    with tempfile.NamedTemporaryFile(
        "w", suffix=".json", delete=False, encoding="utf-8",
    ) as f:
        out_path = Path(f.name)
    try:
        r = subprocess.run(
            [sys.executable, str(SCRIPTS / "audit_assumptions.py"),
             "--no-build", "--json", str(out_path)],
            cwd=REPO, capture_output=True, text=True,
        )
        if r.returncode not in (0, 1):
            return False, []
        try:
            data = json.loads(out_path.read_text(encoding="utf-8"))
            return True, data
        except (json.JSONDecodeError, FileNotFoundError):
            return False, []
    finally:
        out_path.unlink(missing_ok=True)


def run_cleanliness() -> tuple[bool, list[dict]]:
    """Run scripts/check_cleanliness.py and parse its Markdown output."""
    r = subprocess.run(
        [sys.executable, str(SCRIPTS / "check_cleanliness.py"),
         "--no-build"],
        cwd=REPO, capture_output=True, text=True,
    )
    if r.returncode not in (0, 1):
        return False, []
    rows: list[dict] = []
    # Output rows look like:
    #   | `<name>` | **clean**/**LAZY**/**ERROR** | <refs or (none)> |
    for ln in r.stdout.splitlines():
        m = re.match(
            r"\|\s*`([^`]+)`\s*\|\s*\*\*(clean|LAZY|ERROR)\*\*\s*\|\s*(.+?)\s*\|",
            ln,
        )
        if m:
            rows.append({
                "name": m.group(1),
                "status": m.group(2),
                "refs": m.group(3),
            })
    return True, rows


def file_metrics() -> list[dict]:
    """Per-.v-file: name, line count.  Skips DEFAULT_EXCLUDE."""
    # Stay aligned with scripts/build.py.
    excluded = {"Graveyard.v", "Shenannigans.v", "System_F.v"}
    rows: list[dict] = []
    for p in sorted(list(REPO.glob("*.v")) + list(REPO.glob("sandbox/*.v"))):
        if p.name in excluded:
            continue
        try:
            lines = sum(1 for _ in p.read_text(encoding="utf-8").splitlines())
        except OSError:
            lines = 0
        rows.append({
            "path": p.relative_to(REPO).as_posix(),
            "logical": p.relative_to(REPO).with_suffix("").as_posix().replace("/", "."),
            "lines": lines,
        })
    return rows


def git_head() -> str:
    try:
        r = subprocess.run(
            ["git", "log", "--oneline", "-1"],
            cwd=REPO, capture_output=True, text=True, check=True,
        )
        return r.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "(git not available)"


def render(timings: dict[str, float], audit: list[dict], cleanliness: list[dict],
           files: list[dict], head: str) -> str:
    out: list[str] = []
    out.append("# Sandbox status")
    out.append("")
    out.append(f"_Generated {datetime.now().isoformat(timespec='seconds')}._")
    out.append(f"_HEAD: `{head}`_")
    out.append("")

    # ---- Section: build ----
    out.append("## Build times")
    out.append("")
    out.append("| Module | Compile time |")
    out.append("|---|---|")
    if timings:
        for k in sorted(timings):
            v = timings[k]
            out.append(f"| `{k}` | {v:.2f}s |")
    else:
        out.append("| _no build data_ | |")
    total = sum(timings.values())
    out.append("")
    out.append(f"_Total: {total:.2f}s across {len(timings)} module(s)_")
    out.append("")

    # ---- Section: audit ----
    out.append("## Print Assumptions")
    out.append("")
    if audit:
        out.append("| Theorem | Status | Axioms |")
        out.append("|---|---|---|")
        for r in audit:
            thm = "`" + r["theorem"] + "`"
            if r["status"] == "OK":
                status, ax = "**OK**", "(closed)"
            elif r["status"] == "AXIOMS":
                status = "**AXIOMS**"
                ax = ", ".join("`" + a + "`" for a in r["axioms"]) or "(unparsed)"
            else:
                status, ax = "**UNKNOWN**", "(could not parse)"
            out.append(f"| {thm} | {status} | {ax} |")
    else:
        out.append("_audit unavailable_")
    out.append("")

    # ---- Section: cleanliness ----
    out.append("## Definition cleanliness (don't-be-lazy rule)")
    out.append("")
    if cleanliness:
        out.append("| Candidate | Status | Banned references |")
        out.append("|---|---|---|")
        for r in cleanliness:
            out.append(
                f"| `{r['name']}` | **{r['status']}** | {r['refs']} |"
            )
    else:
        out.append("_cleanliness check unavailable_")
    out.append("")

    # ---- Section: files ----
    out.append("## Files")
    out.append("")
    out.append("| File | Logical name | Lines |")
    out.append("|---|---|---|")
    for f in files:
        out.append(f"| `{f['path']}` | `{f['logical']}` | {f['lines']} |")
    out.append("")

    # ---- Footer ----
    n_ok = sum(1 for r in audit if r["status"] == "OK")
    n_ax = sum(1 for r in audit if r["status"] == "AXIOMS")
    n_clean = sum(1 for r in cleanliness if r["status"] == "clean")
    n_lazy = sum(1 for r in cleanliness if r["status"] == "LAZY")
    out.append("## Summary")
    out.append("")
    out.append(f"* Theorems audited: {len(audit)}  "
               f"(**OK**: {n_ok}, **AXIOMS**: {n_ax})")
    out.append(f"* Cleanliness candidates: {len(cleanliness)}  "
               f"(**clean**: {n_clean}, **LAZY**: {n_lazy})")
    out.append(f"* Files tracked: {len(files)}  "
               f"({sum(f['lines'] for f in files)} lines total)")
    out.append("")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--out", default="STATUS.md",
                        help="output Markdown file (default STATUS.md)")
    parser.add_argument("--stdout", action="store_true",
                        help="print to stdout instead of writing a file")
    parser.add_argument("--no-cleanliness", action="store_true",
                        help="skip the cleanliness check (saves ~30s)")
    args = parser.parse_args()

    print("[status] running build...", file=sys.stderr)
    build_ok, _, timings = run_build()
    if not build_ok:
        print("[status] build failed; continuing with partial data",
              file=sys.stderr)

    print("[status] running audit_assumptions...", file=sys.stderr)
    audit_ok, audit_rows = run_audit()

    cleanliness_rows: list[dict] = []
    if not args.no_cleanliness:
        print("[status] running check_cleanliness...", file=sys.stderr)
        _, cleanliness_rows = run_cleanliness()

    files = file_metrics()
    head = git_head()

    md = render(timings, audit_rows, cleanliness_rows, files, head)

    if args.stdout:
        try:
            sys.stdout.reconfigure(encoding="utf-8")
        except Exception:
            pass
        print(md)
    else:
        out_path = REPO / args.out if not Path(args.out).is_absolute() else Path(args.out)
        out_path.write_text(md + "\n", encoding="utf-8")
        print(f"[status] wrote {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()

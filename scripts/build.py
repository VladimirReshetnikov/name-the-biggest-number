#!/usr/bin/env python3
"""Topological build for the name-the-biggest-number Coq sandbox.

Discovers all .v files at the repo root and in sandbox/, parses [Require]
lines to build a dependency graph, topologically sorts, and rebuilds any
file whose .vo is older than the .v or any dependency's .vo.

Usage:
    python scripts/build.py                  # build only stale files
    python scripts/build.py --force          # rebuild everything
    python scripts/build.py --clean          # remove all .vo first
    python scripts/build.py --check          # also run coqchk after each build
    python scripts/build.py FILE             # build FILE and its prerequisites

Run from any working directory; the script anchors on its own location.

The script honours the [_CoqProject] convention by always invoking coqc
with [-Q . ""].  It tolerates missing files in the dependency graph
(stdlib requires like Arith / Lia are silently ignored).

Exit code is 0 on full success, 1 on the first compile or coqchk failure,
2 on usage errors.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
REQUIRE_RE = re.compile(
    r"^\s*Require\s+(?:Import\s+|Export\s+)?([A-Za-z0-9_.\s]+?)\.\s*$",
    re.MULTILINE,
)
NOISE_PATTERNS = (
    "deprecated-",
    "Loading Stdlib",
    "From Stdlib Require",
    "for compatibility",
    "abstract-large-number",
    "Warning:",
)

# Files at the repo root that are historical / archival / paradox-using
# and would either time out or import broken machinery on a fresh build.
# Skipped unless [--all] is passed or the file is named explicitly on the
# command line.
DEFAULT_EXCLUDE = {
    "Graveyard.v",       # tower of 42^42^... that vm_compute can't typecheck
    "Shenannigans.v",    # Hurkens paradox; only built by humans deliberately
    "System_F.v",        # legacy file that doesn't compile on Rocq 9.0.1
                         # (uses removed [beq_nat_true] etc.); kept as
                         # reference material per IDEAS.md Approach B notes
}


def find_v_files(include_excluded: bool = False) -> list[Path]:
    """Return .v paths (relative to REPO) that we manage."""
    paths: list[Path] = []
    for p in sorted(REPO.glob("*.v")):
        if not include_excluded and p.name in DEFAULT_EXCLUDE:
            continue
        paths.append(p.relative_to(REPO))
    for p in sorted(REPO.glob("sandbox/*.v")):
        paths.append(p.relative_to(REPO))
    return paths


def logical_name(rel: Path) -> str:
    """Coq logical module name under -Q . ""."""
    s = rel.as_posix()
    if s.endswith(".v"):
        s = s[:-2]
    return s.replace("/", ".")


def parse_requires(v_path: Path) -> list[str]:
    text = v_path.read_text(encoding="utf-8")
    deps: list[str] = []
    for m in REQUIRE_RE.finditer(text):
        deps.extend(m.group(1).split())
    return deps


def build_graph(v_files: list[Path]) -> tuple[dict[str, Path], dict[str, list[str]]]:
    name_to_path = {logical_name(p): p for p in v_files}
    name_to_deps: dict[str, list[str]] = {}
    for name, rel in name_to_path.items():
        deps = parse_requires(REPO / rel)
        name_to_deps[name] = [d for d in deps if d in name_to_path]
    return name_to_path, name_to_deps


def topo_sort(name_to_deps: dict[str, list[str]]) -> list[str]:
    order: list[str] = []
    state: dict[str, str] = {n: "pending" for n in name_to_deps}

    def visit(n: str, path: list[str]) -> None:
        if state[n] == "done":
            return
        if state[n] == "visiting":
            cycle = " -> ".join(path + [n])
            raise RuntimeError(f"dependency cycle: {cycle}")
        state[n] = "visiting"
        for d in name_to_deps[n]:
            visit(d, path + [n])
        state[n] = "done"
        order.append(n)

    for n in list(name_to_deps):
        visit(n, [])
    return order


def is_stale(name: str, n2p: dict[str, Path], n2d: dict[str, list[str]]) -> bool:
    v_path = REPO / n2p[name]
    vo_path = v_path.with_suffix(".vo")
    if not vo_path.exists():
        return True
    vo_mtime = vo_path.stat().st_mtime
    if v_path.stat().st_mtime > vo_mtime:
        return True
    for d in n2d[name]:
        d_vo = (REPO / n2p[d]).with_suffix(".vo")
        if not d_vo.exists() or d_vo.stat().st_mtime > vo_mtime:
            return True
    return False


def filter_noise(text: str) -> str:
    return "\n".join(
        ln for ln in text.splitlines()
        if ln.strip() and not any(p in ln for p in NOISE_PATTERNS)
    )


def run(cmd: list[str], timeout_sec: int) -> tuple[bool, float, str]:
    start = time.time()
    try:
        r = subprocess.run(
            cmd, cwd=REPO, capture_output=True, text=True, timeout=timeout_sec,
        )
        elapsed = time.time() - start
        return r.returncode == 0, elapsed, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return False, float(timeout_sec), f"TIMEOUT after {timeout_sec}s"


def coqc(v_path: Path, timeout_sec: int = 300) -> tuple[bool, float, str]:
    return run(["coqc", "-Q", ".", "", str(v_path)], timeout_sec)


def coqchk(name: str, timeout_sec: int = 300) -> tuple[bool, float, str]:
    return run(["coqchk", "-Q", ".", "", name], timeout_sec)


def clean() -> None:
    removed = 0
    for ext in (".vo", ".vos", ".vok", ".glob", ".aux"):
        for pattern in (f"*{ext}", f"sandbox/*{ext}", f"sandbox/.*{ext}"):
            for p in REPO.glob(pattern):
                p.unlink(missing_ok=True)
                removed += 1
    print(f"[clean] removed {removed} build artefacts")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--clean", action="store_true",
                        help="remove all .vo / .vos / .vok / .glob / .aux files first")
    parser.add_argument("--check", action="store_true",
                        help="also coqchk every successfully built module")
    parser.add_argument("--force", action="store_true",
                        help="rebuild even if .vo is up-to-date")
    parser.add_argument("--all", action="store_true",
                        help=("include archival / paradox files in the build "
                              "(by default %s are skipped)" % ", ".join(sorted(DEFAULT_EXCLUDE))))
    parser.add_argument("--timeout", type=int, default=300,
                        help="per-file timeout in seconds (default 300)")
    parser.add_argument("file", nargs="?",
                        help="build only this file (and its prerequisites)")
    args = parser.parse_args()

    v_files = find_v_files(include_excluded=args.all or args.file is not None)
    if not v_files:
        print("no .v files found", file=sys.stderr)
        sys.exit(2)

    n2p, n2d = build_graph(v_files)
    try:
        order = topo_sort(n2d)
    except RuntimeError as e:
        print(f"error: {e}", file=sys.stderr)
        sys.exit(2)

    if args.file:
        rel = Path(args.file)
        if rel.is_absolute():
            try:
                rel = rel.relative_to(REPO)
            except ValueError:
                print(f"error: {args.file} is outside repo", file=sys.stderr)
                sys.exit(2)
        target = logical_name(rel)
        if target not in n2p:
            print(f"error: {args.file} not in build graph", file=sys.stderr)
            sys.exit(2)
        keep: set[str] = set()
        stack = [target]
        while stack:
            n = stack.pop()
            if n in keep:
                continue
            keep.add(n)
            stack.extend(n2d[n])
        order = [n for n in order if n in keep]

    if args.clean:
        clean()

    built = skipped = 0
    total_elapsed = 0.0
    fail: str | None = None

    for name in order:
        rel = n2p[name]
        if not args.force and not is_stale(name, n2p, n2d):
            print(f"  ok    {name:<40}  (.vo up to date)")
            skipped += 1
            continue

        print(f"  build {name:<40}  ...", end=" ", flush=True)
        ok, elapsed, output = coqc(rel, args.timeout)
        total_elapsed += elapsed
        if not ok:
            print(f"FAILED ({elapsed:.2f}s)")
            print(filter_noise(output))
            fail = name
            break
        print(f"{elapsed:6.2f}s")
        built += 1

        if args.check:
            ok_chk, elapsed_chk, output_chk = coqchk(name, args.timeout)
            total_elapsed += elapsed_chk
            if not ok_chk:
                print(f"  coqchk FAILED for {name} ({elapsed_chk:.2f}s)")
                print(filter_noise(output_chk))
                fail = name
                break
            print(f"  check {name:<40}  {elapsed_chk:6.2f}s")

    print()
    print(f"summary: {built} built, {skipped} up-to-date, "
          f"{total_elapsed:.2f}s total")
    if fail:
        print(f"FAILED at {fail}")
        sys.exit(1)


if __name__ == "__main__":
    main()

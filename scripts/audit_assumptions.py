#!/usr/bin/env python3
"""Run [Print Assumptions T] across all interesting theorems and definitions
in the repo, and report which are axiom-free.

Auto-discovers theorems whose names match [contender_*_lt_*] (the strict-
inequality theorems each contender file is centred on) plus a small fixed
list of extras (e.g. [Contender.contender_5], [sandbox.Brouwer.BigGrow]).

Usage:
    python scripts/audit_assumptions.py                # print Markdown table
    python scripts/audit_assumptions.py --md FILE      # also write to FILE
    python scripts/audit_assumptions.py --json FILE    # machine-readable copy
    python scripts/audit_assumptions.py --no-build     # skip the rebuild step

The script needs every relevant .vo to exist; by default it invokes
[scripts/build.py] first to refresh anything stale.

Output column meanings:

    Theorem         qualified Coq name
    Status          OK if [Print Assumptions] reports a closed global context,
                    AXIOMS otherwise
    Axioms          comma-separated list of axiom identifiers (or "none")

Exit code is 0 if every theorem closes under the global context, 1 if any
theorem depends on axioms, 2 on usage / infrastructure errors.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]

# Files we deliberately don't audit because they are archival, paradox-using,
# or simply don't compile on the current Coq version.  Mirrors
# scripts/build.py's DEFAULT_EXCLUDE.
DEFAULT_EXCLUDE = {
    "Graveyard.v",
    "Shenannigans.v",
    "System_F.v",
}

MODULE_OPEN_RE = re.compile(
    r"^\s*Module\s+(?!Type\b|Import\b)(\w+)\s*(?:\.\s*$|:)", re.MULTILINE,
)
MODULE_CLOSE_RE = re.compile(r"^\s*End\s+(\w+)\s*\.\s*$", re.MULTILINE)
THEOREM_RE = re.compile(
    r"^\s*(?:Theorem|Lemma|Corollary)\s+(contender_\w*?_lt_\w+)\b",
    re.MULTILINE,
)


def strip_coq_comments(text: str) -> str:
    """Replace Coq (* ... *) comments with spaces of the same length, so
    line and column offsets match the original.  Handles nested comments.
    Strings are left as-is (we don't care about them for our scan)."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if depth == 0 and text[i:i + 2] == "(*":
            depth = 1
            out.append("  ")
            i += 2
        elif depth > 0 and text[i:i + 2] == "(*":
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and text[i:i + 2] == "*)":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)

# Extra named entities to audit alongside the auto-discovered theorems.
# Each entry is (qualified_name, file_logical_name_to_Require).
EXTRAS: list[tuple[str, str]] = [
    ("Contender.contender_5", "Contender"),
    ("sandbox.Brouwer.BigGrow", "sandbox.Brouwer"),
    ("sandbox.Brouwer.epsilon_0", "sandbox.Brouwer"),
    ("sandbox.Brouwer.FGH", "sandbox.Brouwer"),
    ("sandbox.BrouwerHigh.epsilon_omega", "sandbox.BrouwerHigh"),
    ("sandbox.BrouwerHigh.pseudo_Gamma_0", "sandbox.BrouwerHigh"),
]

NOISE_PATTERNS = (
    "deprecated-",
    "Loading Stdlib",
    "From Stdlib Require",
    "for compatibility",
    "Warning:",
)


def file_logical_name(rel: Path) -> str:
    s = rel.as_posix()
    if s.endswith(".v"):
        s = s[:-2]
    return s.replace("/", ".")


def discover_theorems() -> list[tuple[str, str]]:
    """Find (qualified_name, file_logical_name) for every contender_*_lt_* in
    the tracked .v files, taking surrounding [Module X.] / [End X.] into
    account.
    """
    out: list[tuple[str, str]] = []
    for v in sorted(list(REPO.glob("*.v")) + list(REPO.glob("sandbox/*.v"))):
        if v.name in DEFAULT_EXCLUDE:
            continue
        rel = v.relative_to(REPO)
        file_mod = file_logical_name(rel)
        text = strip_coq_comments(v.read_text(encoding="utf-8"))

        events: list[tuple[int, str, str]] = []
        for m in MODULE_OPEN_RE.finditer(text):
            events.append((m.start(), "open", m.group(1)))
        for m in MODULE_CLOSE_RE.finditer(text):
            events.append((m.start(), "close", m.group(1)))
        for m in THEOREM_RE.finditer(text):
            events.append((m.start(), "thm", m.group(1)))
        events.sort(key=lambda e: e[0])

        stack: list[str] = []
        for _, kind, name in events:
            if kind == "open":
                stack.append(name)
            elif kind == "close":
                if stack and stack[-1] == name:
                    stack.pop()
            else:  # thm
                qual = ".".join([file_mod] + stack + [name])
                out.append((qual, file_mod))
    return out


def make_audit_script(entries: list[tuple[str, str]]) -> str:
    """Produce the .v source whose stdout we will parse."""
    lines: list[str] = []
    seen: set[str] = set()
    for _, mod in entries:
        if mod not in seen:
            lines.append(f"Require {mod}.")
            seen.add(mod)
    lines.append("")
    for qual, _ in entries:
        lines.append(f"Print Assumptions {qual}.")
    lines.append("")
    return "\n".join(lines)


def filter_noise(text: str) -> str:
    return "\n".join(
        ln for ln in text.splitlines()
        if ln.strip() and not any(p in ln for p in NOISE_PATTERNS)
    )


def run_coqc(audit_v: Path, timeout_sec: int = 300) -> tuple[bool, str]:
    r = subprocess.run(
        ["coqc", "-Q", ".", "", str(audit_v)],
        cwd=REPO, capture_output=True, text=True, timeout=timeout_sec,
    )
    return r.returncode == 0, r.stdout + r.stderr


# Coq prints either:
#   Closed under the global context
# or:
#   Axioms:
#   <axiom ident> : <axiom type spanning N lines>
#   <axiom ident> : <axiom type ...>
#
# We split the whole stdout into per-theorem blocks by looking for the
# next "Print Assumptions ..." marker that coqc prints back.  But coqc
# doesn't echo prompts; instead each block is delimited by either
# "Closed under the global context" or an "Axioms:" header followed by
# axiom entries.  So we walk the output linearly keeping a current block.

CLOSED_RE = re.compile(r"^Closed under the global context\.?\s*$", re.MULTILINE)
AXIOMS_HEADER_RE = re.compile(r"^Axioms:\s*$", re.MULTILINE)
AXIOM_ENTRY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", re.MULTILINE)


def parse_assumptions(stdout: str, count: int) -> list[tuple[str, list[str]]]:
    """Return a list of (status, axioms) per theorem, in order.

    [status] is "OK" or "AXIOMS"; [axioms] is the list of axiom idents
    (empty when status is OK).
    """
    text = filter_noise(stdout)
    # Split on transitions between "Closed under..." / "Axioms:" markers.
    # We scan tokens left to right.
    results: list[tuple[str, list[str]]] = []
    i = 0
    while i < len(text) and len(results) < count:
        closed = CLOSED_RE.search(text, i)
        ax_hdr = AXIOMS_HEADER_RE.search(text, i)
        next_closed = closed.start() if closed else len(text) + 1
        next_axiom = ax_hdr.start() if ax_hdr else len(text) + 1
        if next_closed < next_axiom:
            results.append(("OK", []))
            i = closed.end()  # type: ignore[union-attr]
        elif next_axiom < next_closed:
            block_end = min(next_closed, len(text))
            # find the start of the *next* block (next "Closed" or "Axioms:")
            after = ax_hdr.end()  # type: ignore[union-attr]
            following_closed = CLOSED_RE.search(text, after)
            following_axiom = AXIOMS_HEADER_RE.search(text, after)
            stops = [s.start() for s in (following_closed, following_axiom) if s]
            block_end = min(stops) if stops else len(text)
            block = text[after:block_end]
            ax = [m.group(1) for m in AXIOM_ENTRY_RE.finditer(block)]
            results.append(("AXIOMS", ax))
            i = block_end
        else:
            break
    while len(results) < count:
        results.append(("UNKNOWN", []))
    return results


def render_md(table: list[dict]) -> str:
    rows = ["| Theorem | Status | Axioms |", "|---|---|---|"]
    for r in table:
        thm = "`" + r["theorem"] + "`"
        if r["status"] == "OK":
            status = "**OK**"
            ax = "(closed)"
        elif r["status"] == "AXIOMS":
            status = "**AXIOMS**"
            ax = ", ".join("`" + a + "`" for a in r["axioms"]) or "(unparsed)"
        else:
            status = "**UNKNOWN**"
            ax = "(could not parse)"
        rows.append(f"| {thm} | {status} | {ax} |")
    return "\n".join(rows)


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--md", metavar="FILE",
                        help="also write the Markdown report to FILE")
    parser.add_argument("--json", metavar="FILE",
                        help="also write a JSON copy of the results to FILE")
    parser.add_argument("--no-build", action="store_true",
                        help="skip the [scripts/build.py] step")
    parser.add_argument("--timeout", type=int, default=300,
                        help="coqc timeout in seconds (default 300)")
    args = parser.parse_args()

    if not args.no_build:
        build_py = REPO / "scripts" / "build.py"
        r = subprocess.run([sys.executable, str(build_py)], cwd=REPO)
        if r.returncode != 0:
            print("[audit] build failed; aborting", file=sys.stderr)
            sys.exit(1)

    discovered = discover_theorems()
    entries: list[tuple[str, str]] = []
    seen_quals: set[str] = set()
    for q, m in discovered + EXTRAS:
        if q in seen_quals:
            continue
        seen_quals.add(q)
        entries.append((q, m))

    if not entries:
        print("[audit] no theorems discovered", file=sys.stderr)
        sys.exit(2)

    script = make_audit_script(entries)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".v", dir=REPO, delete=False, encoding="utf-8",
    ) as f:
        audit_v = Path(f.name)
        f.write(script)

    try:
        ok, stdout = run_coqc(audit_v, args.timeout)
        if not ok:
            print("[audit] coqc failed:", file=sys.stderr)
            print(filter_noise(stdout), file=sys.stderr)
            sys.exit(2)
        results = parse_assumptions(stdout, len(entries))
    finally:
        for ext in (".v", ".vo", ".vos", ".vok", ".glob", ".aux"):
            p = audit_v.with_suffix(ext)
            p.unlink(missing_ok=True)

    table = []
    bad = 0
    for (qual, _), (status, ax) in zip(entries, results):
        table.append({"theorem": qual, "status": status, "axioms": ax})
        if status != "OK":
            bad += 1

    md = render_md(table)
    print(md)
    print()
    print(f"summary: {len(table) - bad} OK, {bad} not closed")

    if args.md:
        Path(args.md).write_text(md + "\n", encoding="utf-8")
    if args.json:
        Path(args.json).write_text(
            json.dumps(table, indent=2) + "\n", encoding="utf-8",
        )

    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()

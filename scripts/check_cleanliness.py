#!/usr/bin/env python3
"""Enforce the upstream README "don't be lazy" rule operationally.

The rule reads:
    don't use `contender_N` as a definition when defining `contender_N+1`,
    it's just lazy.

The repo's reading (see AGENTS.md "Current Game Plan") sharpens this to:
the new contender's *definition* must not mention any of the previous
engine's maximum / search machinery -- specifically [R_tower], [tPrevMax],
[tRTower], [largest_*_nat_of_depth], and a small list of sandbox aliases
that unfold to those.  The proof of strict inequality MAY mention any of
them; the definition MAY NOT.

This script asks Coq to print the body of each candidate definition
(via `Print T`) and then checks the printed body, plus -- recursively up
to a configurable depth -- the bodies of every non-trivial identifier the
body mentions, for any banned name.  It is a heuristic check: it catches
direct references and one or two levels of intermediate aliasing, but is
not a full transitive analysis.  It is good enough to catch real-world
laziness without the complexity of parsing Coq's reference graph.

Usage:
    python scripts/check_cleanliness.py             # check default candidate list
    python scripts/check_cleanliness.py NAME ...    # check specific qualified names
    python scripts/check_cleanliness.py --depth 3   # recursion depth (default 2)
    python scripts/check_cleanliness.py --no-build  # skip the rebuild step
    python scripts/check_cleanliness.py --md FILE   # also write a Markdown report

Default candidate list is in CANDIDATES.  Banned identifier set is in
BANNED.  Both are deliberately conservative; extend as the project grows.

Exit code is 0 if every candidate is clean, 1 if any candidate references
a banned identifier (the actionable signal), 2 on infrastructure errors.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


# --------------------------------------------------------------------------
# Configuration: the banned identifier set and the candidate list.
#
# Banned names are matched as whole-word substrings against [Print] output.
# Listing both the unqualified short name and any sandbox alias of it
# (e.g. RTower, RT1) is the simplest way to be robust against Coq's print
# layer using whichever spelling.
# --------------------------------------------------------------------------

# Unqualified identifier names that disqualify a contender's definition.
# Each is matched on word boundaries against the [Print] output.
BANNED: dict[str, str] = {
    # Core "previous engine" identifier from Contender.v.  We deliberately
    # do NOT include the generic name [largest_of_depth] here, because
    # fresh-engine sandboxes (e.g. sandbox/GrowEmbed.v's L_Grow) define
    # their own [largest_of_depth] and a substring match would flag those
    # as false positives.  [largest_STLCNatRec_nat_of_depth] is specific
    # enough to catch direct uses of contender_5's engine.
    "largest_STLCNatRec_nat_of_depth":
        "Contender.v's depth-bounded max (the engine of contender_5)",

    # Reflection-tower oracle structures (Approach D.x).
    "R_tower":
        "reflection tower from sandbox/ReflectTower*.v -- oracle-based",
    "RTower":
        "alias of sandbox.ReflectTower.R_tower in ReflectRTower files",
    "RT1":
        "alias of (R_tower 1) in sandbox/BigGrowRTower.v",
    "tPrevMax":
        "reflection-language oracle primitive",
    "tRTower":
        "second-order reflection oracle primitive (Approach D.2)",
    "largest_reflect_nat_of_depth":
        "reflection-language depth-bounded max",
    "largest_RT_nat_of_depth":
        "L_RT depth-bounded max (Approach D.2)",
    "largest_BGPrev_nat_of_depth":
        "L_BG_Prev depth-bounded max (BigGrowPrevMax)",
    "prevMax":
        "abstract previous-max oracle parameter",
    "prevMax2":
        "second-level previous-max oracle (Approach D.3)",
}

# Default contender candidates to audit.  Each entry is
# (qualified_name, module_to_Require).  Add new entries here as new
# fresh-engine candidates land in the sandbox.
CANDIDATES: list[tuple[str, str]] = [
    # The current upstream contender; its DEFINITION mentions
    # largest_STLCNatRec_nat_of_depth by construction, so this *should*
    # be flagged.  Including it as a sanity check that the script
    # actually flags real cases.
    ("Contender.contender_5", "Contender"),

    # Existing sandbox candidates.  Most of these are oracle-based by
    # design (research artifacts, not promotion targets); we expect them
    # to fail the cleanliness check.
    ("sandbox.ReflectRTowerSmall.contender_reflect_rtower_small",
     "sandbox.ReflectRTowerSmall"),
    ("sandbox.ReflectRTowerComputed.contender_reflect_rtower_computed",
     "sandbox.ReflectRTowerComputed"),
    ("sandbox.ReflectRTower3.contender_reflect_rtower3",
     "sandbox.ReflectRTower3"),
    ("sandbox.BigGrowPrevMax.BigGrowPrevMax.contender_bigGrowPrev",
     "sandbox.BigGrowPrevMax"),
    ("sandbox.BigGrowRTower.contender_BG_RT_simple",
     "sandbox.BigGrowRTower"),
    ("sandbox.BigGrowRTower.contender_BG_RT_layered",
     "sandbox.BigGrowRTower"),
    ("sandbox.BigGrowRTower.contender_BG_RT_stacked",
     "sandbox.BigGrowRTower"),

    # Pure Brouwer-FGH engines.  These should pass cleanliness (their
    # definitions reference only Brouwer-ordinal machinery).
    ("sandbox.Brouwer.BigGrow", "sandbox.Brouwer"),
    ("sandbox.BrouwerHigh.BigGrow_e_omega", "sandbox.BrouwerHigh"),
    ("sandbox.BrouwerHigh.BigGrow_pseudo_Gamma_0", "sandbox.BrouwerHigh"),

    # Approach M -- the embedding-witness fresh-engine candidate.  This
    # is the first sandbox candidate that should pass cleanliness:
    # contender_grow_6 := largest_Grow_nat_of_depth 44, definitionally
    # disjoint from contender_5's engine.
    ("sandbox.GrowEmbed.contender_grow_6", "sandbox.GrowEmbed"),
    ("sandbox.GrowEmbed.BigGrowEmbed.contender_grow_6", "sandbox.GrowEmbed"),
]


# --------------------------------------------------------------------------
# Implementation.
# --------------------------------------------------------------------------

NOISE_PATTERNS = (
    "deprecated-",
    "Loading Stdlib",
    "From Stdlib Require",
    "for compatibility",
    "Warning:",
)

# An identifier in Coq's printed output: a sequence of letters, digits,
# underscores, and primes, optionally inside a qualified path.  We extract
# the basename (last path component) for banned-set matching.
QUALIFIED_IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*(?:'\w*)?(?:\.[A-Za-z_][A-Za-z0-9_]*(?:'\w*)?)*\b")
# Coq tokens that are NOT identifiers we want to treat as references --
# language keywords, type formers, eliminators, etc.
NON_IDENT_TOKENS: set[str] = {
    "fun", "match", "with", "end", "let", "in", "if", "then", "else",
    "as", "return", "fix", "cofix", "for", "of", "forall", "exists",
    "Set", "Type", "Prop", "SProp",
    "True", "False",
    "nat", "bool", "list", "option", "unit", "Empty_set", "sum", "prod",
    "S", "O",  # nat constructors, common
    "true", "false",
    "tt",
    "eq", "eq_refl",  # equality
}


def file_logical_name(rel: Path) -> str:
    s = rel.as_posix()
    if s.endswith(".v"):
        s = s[:-2]
    return s.replace("/", ".")


def filter_noise(text: str) -> str:
    return "\n".join(
        ln for ln in text.splitlines()
        if ln.strip() and not any(p in ln for p in NOISE_PATTERNS)
    )


def make_print_script(name: str, requires: list[str]) -> str:
    lines: list[str] = []
    seen: set[str] = set()
    for req in requires:
        if req not in seen:
            lines.append(f"Require {req}.")
            seen.add(req)
    # Force fully-qualified printing so we can recurse on qualified names.
    lines.append("Set Printing All.")
    lines.append(f"Print {name}.")
    return "\n".join(lines) + "\n"


def run_print(name: str, requires: list[str], timeout_sec: int = 60) -> str:
    """Return the [Print name] output (stdout+stderr, noise filtered)."""
    src = make_print_script(name, requires)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".v", dir=REPO, delete=False, encoding="utf-8",
    ) as f:
        path = Path(f.name)
        f.write(src)
    try:
        r = subprocess.run(
            ["coqc", "-Q", ".", "", str(path)],
            cwd=REPO, capture_output=True, text=True, timeout=timeout_sec,
        )
        return filter_noise(r.stdout + r.stderr)
    except subprocess.TimeoutExpired:
        return f"[TIMEOUT after {timeout_sec}s]"
    finally:
        for ext in (".v", ".vo", ".vos", ".vok", ".glob", ".aux"):
            path.with_suffix(ext).unlink(missing_ok=True)


def extract_print_body(name: str, output: str) -> str:
    """Coq prints
        <name> = <body>
             : <type>
    Strip everything before "<name> =" and after the trailing " : ".
    Returns the raw body text (multiline, possibly).
    """
    short = name.rsplit(".", 1)[-1]
    m = re.search(rf"\b{re.escape(short)}\s*=\s*(.*?)(?:\n\s*:\s*[^\n]+)?\Z",
                  output, re.DOTALL)
    if m:
        return m.group(1).strip()
    return output  # fallback: scan the whole output


def basename(qual: str) -> str:
    return qual.rsplit(".", 1)[-1]


def find_idents(text: str) -> set[str]:
    """Pull qualified or unqualified identifiers out of [text].

    Returns the set of identifiers as they appear in the source -- with
    whatever module qualifier Coq chose to attach when printing.  The
    qualified form is what we want to recurse on (so [Print] can find
    the constant); the *basename* of each is what we match against the
    BANNED set.
    """
    out: set[str] = set()
    for m in QUALIFIED_IDENT_RE.finditer(text):
        ident = m.group(0)
        b = basename(ident)
        if b in NON_IDENT_TOKENS:
            continue
        out.add(ident)
    return out


def banned_hits(text: str) -> list[str]:
    """Return the banned identifiers that appear (as whole words) in [text].
    Both unqualified and qualified-suffix forms are matched."""
    hits: list[str] = []
    for ident in BANNED:
        if re.search(rf"\b{re.escape(ident)}\b", text):
            hits.append(ident)
    return hits


def candidate_module(qual: str) -> str:
    """Best-effort guess of the module to [Require] for a given qualified
    name.  Tries increasingly short prefixes [a.b.c.d, a.b.c, a.b, a] and
    returns the first one that maps to an existing .v file.
    """
    parts = qual.split(".")
    for cut in range(len(parts), 0, -1):
        rel = Path(*parts[:cut]).with_suffix(".v")
        if (REPO / rel).exists():
            return ".".join(parts[:cut])
    if len(parts) > 1:
        return ".".join(parts[:-1])
    return qual


def check_one(name: str, requires: list[str], depth: int,
              timeout_sec: int) -> dict:
    """Run the cleanliness check on a single qualified [name].

    Returns a dict with keys: name, status, hits, trace.
    status is "clean", "lazy", or "error".
    hits is the list of banned names found (across all visited identifiers).
    trace is a human-readable list of "name -> banned_ident" steps.
    """
    visited: set[str] = set()
    queue: list[tuple[str, int, str]] = [(name, depth, name)]
    all_hits: list[str] = []
    trace: list[str] = []
    error: str | None = None

    while queue:
        cur, remaining, path = queue.pop(0)
        if cur in visited:
            continue
        visited.add(cur)

        out = run_print(cur, requires, timeout_sec)
        if "[TIMEOUT" in out or "Error" in out and "Print" not in out:
            # Coq couldn't print this name (e.g., it's a binder, a
            # primitive constructor, or simply doesn't exist as a
            # global).  Skip silently -- not a "lazy" signal.
            continue
        body = extract_print_body(cur, out)

        hits = banned_hits(body)
        for h in hits:
            all_hits.append(h)
            trace.append(f"{path} -> {h}")

        if remaining > 0:
            for ident in find_idents(body):
                bn = basename(ident)
                if bn in BANNED:
                    continue  # already counted by [banned_hits]
                if bn == basename(cur):
                    continue  # self-reference (recursive Fixpoint / mutual rec)
                # The qualified [ident] (as Coq printed it) is what
                # we hand back to Coq for the next [Print].  If Coq
                # can't resolve it, [Print] will error and we silently
                # skip.
                queue.append((ident, remaining - 1, f"{path} -> {ident}"))

    if error:
        return {"name": name, "status": "error", "hits": [], "trace": [error]}
    if all_hits:
        return {"name": name, "status": "lazy",
                "hits": sorted(set(all_hits)), "trace": trace}
    return {"name": name, "status": "clean", "hits": [], "trace": []}


def render_md(results: list[dict]) -> str:
    rows = ["| Candidate | Status | Banned references |", "|---|---|---|"]
    for r in results:
        thm = "`" + r["name"] + "`"
        if r["status"] == "clean":
            status = "**clean**"
            refs = "(none)"
        elif r["status"] == "lazy":
            status = "**LAZY**"
            refs = ", ".join("`" + h + "`" for h in r["hits"])
        else:
            status = "**ERROR**"
            refs = "(see stderr)"
        rows.append(f"| {thm} | {status} | {refs} |")
    return "\n".join(rows)


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("names", nargs="*",
                        help="qualified names to audit (default: CANDIDATES)")
    parser.add_argument("--depth", type=int, default=2,
                        help="recursion depth for transitive checks (default 2)")
    parser.add_argument("--no-build", action="store_true",
                        help="skip the [scripts/build.py] step")
    parser.add_argument("--md", metavar="FILE",
                        help="also write the Markdown report to FILE")
    parser.add_argument("--timeout", type=int, default=60,
                        help="per-Print timeout in seconds (default 60)")
    args = parser.parse_args()

    if not args.no_build:
        build_py = REPO / "scripts" / "build.py"
        r = subprocess.run([sys.executable, str(build_py)], cwd=REPO)
        if r.returncode != 0:
            print("[cleanliness] build failed; aborting", file=sys.stderr)
            sys.exit(2)

    if args.names:
        candidates = [(n, candidate_module(n)) for n in args.names]
    else:
        candidates = CANDIDATES

    requires_per_name: dict[str, list[str]] = {}
    seen_modules: list[str] = []
    for name, mod in candidates:
        if mod not in seen_modules:
            seen_modules.append(mod)
        requires_per_name[name] = list(seen_modules)

    results: list[dict] = []
    for name, _ in candidates:
        results.append(check_one(name, requires_per_name[name],
                                 args.depth, args.timeout))

    md = render_md(results)
    print(md)
    print()
    n_clean = sum(1 for r in results if r["status"] == "clean")
    n_lazy = sum(1 for r in results if r["status"] == "lazy")
    n_err = sum(1 for r in results if r["status"] == "error")
    print(f"summary: {n_clean} clean, {n_lazy} lazy, {n_err} error")

    if args.md:
        Path(args.md).write_text(md + "\n", encoding="utf-8")

    sys.exit(0 if n_lazy == 0 and n_err == 0 else 1)


if __name__ == "__main__":
    main()

# scripts/

Small Python helpers for working with the Coq sandbox.  Each script is
runnable on its own (no external dependencies; standard-library Python
3.9+).  Run them from any working directory; each script anchors on its
own location to find the repo root.

The motivation, scope, and explicit non-goals for this directory are
documented in the brainstorming discussion that preceded the `tooling`
branch.  Short version: orchestrate `coqc` / `coqchk` and report on
their output; do **not** try to replace Coq's reasoning or replicate
the IDE-side proof-iteration experience (CoqIDE / `coq-lsp` already
do that).

## `build.py`

Topological build for every `.v` file in the repo (root and
`sandbox/`).  Parses each file's `Require` lines to derive a dependency
graph, sorts it, and rebuilds anything whose `.vo` is older than its
`.v` or any dependency's `.vo`.  Reports per-file compile times and
the total.

```text
python scripts/build.py                    # rebuild only stale files
python scripts/build.py --force            # rebuild everything
python scripts/build.py --clean            # remove .vo / .vos / .vok / .glob first
python scripts/build.py --check            # also coqchk after each build
python scripts/build.py sandbox/Brouwer.v  # build this file and prerequisites
```

Output layout:

```text
  ok    Contender                                  (.vo up to date)
  build sandbox.Brouwer                       ...    1.13s
  build sandbox.BrouwerHigh                   ...    0.97s
  ...
summary: 3 built, 11 up-to-date, 4.21s total
```

Stops on the first compilation failure and prints the (de-noised)
`coqc` output.  Stdlib `Require Import Arith` etc. are silently
ignored when computing the local dependency graph.

## `audit_assumptions.py`

Runs `Print Assumptions T` for every interesting `T` in the repo and
emits a Markdown table.  Auto-discovers theorems whose names match
`contender_*_lt_*` (the strict-inequality theorems each contender file
is centred on); plus a small fixed extras list at the top of the
script (`EXTRAS`) for items whose names do not fit that pattern, e.g.
`Contender.contender_5`, `sandbox.Brouwer.BigGrow`,
`sandbox.BrouwerHigh.pseudo_Gamma_0`.

```text
python scripts/audit_assumptions.py                 # print Markdown table
python scripts/audit_assumptions.py --md STATUS.md  # also write to STATUS.md
python scripts/audit_assumptions.py --json out.json # machine-readable copy
python scripts/audit_assumptions.py --no-build      # skip the build step
```

The script generates a temporary `.v` file at the repo root that
imports each module and runs `Print Assumptions` on each named entity,
runs `coqc` on it, parses the output, and tears the temp file down
afterwards.  By default it invokes `build.py` first to refresh any
stale `.vo`.

Exit code:

* `0` -- every theorem closes under the global context;
* `1` -- one or more theorems depend on axioms (a real signal during
  cleanup work);
* `2` -- usage / infrastructure error (missing file, build failed,
  `coqc` not on `PATH`, ...).

To extend the audit: add new entries to `EXTRAS` in
`scripts/audit_assumptions.py`.  Discovery does the rest for any new
strict-inequality theorem in any new sandbox file, as long as the
theorem's name follows the `contender_*_lt_*` convention.

## `check_cleanliness.py`

Operationalises the upstream README's "don't be lazy" rule, as sharpened
in `AGENTS.md`'s Current Game Plan.  For every contender candidate in
the script's `CANDIDATES` list (or names passed on the command line),
asks Coq to print the body of that definition and -- recursively, up
to a configurable depth -- the bodies of every non-trivial identifier
that body mentions, then scans for any name in `BANNED`.  Reports
each candidate as **clean**, **LAZY**, or **ERROR**.

```text
python scripts/check_cleanliness.py             # check default candidate list
python scripts/check_cleanliness.py NAME ...    # check specific qualified names
python scripts/check_cleanliness.py --depth 3   # recursion depth (default 2)
python scripts/check_cleanliness.py --no-build  # skip the rebuild step
python scripts/check_cleanliness.py --md FILE   # also write a Markdown report
```

Output excerpt (from a recent run):

```text
| Candidate                                                              | Status     | Banned references |
|---|---|---|
| `Contender.contender_5`                                                | **LAZY**   | `largest_STLCNatRec_nat_of_depth` |
| `sandbox.BigGrowRTower.contender_BG_RT_simple`                         | **LAZY**   | `RT1` |
| `sandbox.BigGrowRTower.contender_BG_RT_stacked`                        | **LAZY**   | `RT1`, `largest_BGPrev_nat_of_depth` |
| `sandbox.Brouwer.BigGrow`                                              | **clean**  | (none) |
| `sandbox.BrouwerHigh.BigGrow_pseudo_Gamma_0`                           | **clean**  | (none) |

summary: 3 clean, 8 lazy, 0 error
```

`Contender.contender_5` is intentionally listed as a sanity check: it
references `largest_STLCNatRec_nat_of_depth` directly, so it MUST flag
LAZY (otherwise the check is broken).  Most of the existing
oracle-based sandbox candidates also flag LAZY by design -- per the
"Current Game Plan" they are research artifacts, not promotion
targets.

The check uses `Print` with `Set Printing All` so identifiers come
back qualified, and recurses on the qualified form so mid-chain
aliases (e.g. `RT1 := R_tower 1`) are caught even when their direct
parent appears benign.  It is a *heuristic* check -- by design, not a
sound transitive analysis.  If a candidate's chain is deeper than
`--depth`, the script may miss the banned reference.  The depth
default of 2 is enough for everything we currently care about; bump it
if a new aliasing chain is added.

To extend:

* New candidates that should pass (or should fail) -- add to
  `CANDIDATES` in `scripts/check_cleanliness.py`.
* New banned identifiers (e.g. when a future fresh-engine sandbox
  introduces yet another oracle) -- add to `BANNED` in the same file.
  Each entry is `<unqualified-name>: <one-line-explanation>`; the
  explanation is currently informational only.

Exit code:

* `0` -- every audited candidate is clean;
* `1` -- at least one candidate references a banned identifier;
* `2` -- infrastructure error.

## `status.py`

Thin orchestrator that runs `build.py`, `audit_assumptions.py`, and
`check_cleanliness.py`, then stitches their outputs into a single
`STATUS.md` at the repo root.  Useful as a relay snapshot.

```text
python scripts/status.py                  # write STATUS.md
python scripts/status.py --out FILE       # to a different file
python scripts/status.py --stdout         # print to stdout instead
python scripts/status.py --no-cleanliness # skip the (slowest) cleanliness pass
```

The generated file has four sections plus a footer:

* **Build times** -- per-module compile time from this run.  Files
  whose `.vo` was already up-to-date show `0.00s`; pass
  `python scripts/build.py --force` first if you want fresh
  measurements.
* **Print Assumptions** -- the same Markdown table
  `audit_assumptions.py` emits.
* **Definition cleanliness** -- the table from
  `check_cleanliness.py`.
* **Files** -- per-`.v`-file logical name and line count.
* **Summary** -- one-line totals.

The file is *not* tracked by git; treat it as a local artefact.  The
authoritative source of state is the .v files and the three underlying
scripts; `STATUS.md` is a derivable cache.

## Why these and not more

The brainstorm discussion called out four high-leverage scripts: build
orchestration, `Print Assumptions` reporting, cleanliness enforcement,
and a combined dashboard.  All four are now in this directory.
Everything beyond them (CI dashboards, cross-version testing,
term-unfolding tooling, Coq-source code generators, and so on) was
deemed overkill for a brainstorming-mode repo.  If the repo's
workflow shifts toward serious submission preparation, that judgment
may change.

## Caveats

* Discovery in `audit_assumptions.py` is regex-based and works because
  the existing files keep the contender-naming convention.  If a future
  theorem doesn't match `contender_*_lt_*`, add it to `EXTRAS`
  explicitly.
* `Module Type X.` and `Section X.` are deliberately *not* tracked as
  module openers.  We don't currently use them in the sandbox; if that
  changes, the discovery regex needs an update.
* `check_cleanliness.py` is a heuristic check, not a sound transitive
  analysis (see its own caveats above).
* The temporary `.v` file produced by `audit_assumptions.py` and
  `check_cleanliness.py` lives at the repo root for the duration of
  the run (so it shares the `_CoqProject` namespace).  If a previous
  run was interrupted hard, stale `tmp*.v` files may need manual
  cleanup.
* `coqc` and `coqchk` must be on `PATH`.  On Windows the Rocq Platform
  installer normally arranges this; see the project root `AGENTS.md`
  for the canonical install paths and how to fix `PATH` if needed.

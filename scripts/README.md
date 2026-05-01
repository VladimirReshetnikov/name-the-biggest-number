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

## Why these and not more

The brainstorm discussion explicitly called out these two as the
high-leverage scripts; everything beyond them (cleanliness lint, CI
dashboards, cross-version testing, term-unfolding tooling) was deemed
overkill for a brainstorming-mode repo.  If the repo's workflow shifts
toward serious submission preparation, that judgment may change.

## Caveats

* Discovery in `audit_assumptions.py` is regex-based and works because
  the existing files keep the contender-naming convention.  If a future
  theorem doesn't match `contender_*_lt_*`, add it to `EXTRAS`
  explicitly.
* `Module Type X.` and `Section X.` are deliberately *not* tracked as
  module openers.  We don't currently use them in the sandbox; if that
  changes, the discovery regex needs an update.
* The temporary `.v` file produced by `audit_assumptions.py` lives at
  the repo root for the duration of the run (so it shares the
  `_CoqProject` namespace).  If a previous run was interrupted hard,
  stale `tmp*.v` files may need manual cleanup.
* `coqc` and `coqchk` must be on `PATH`.  On Windows the Rocq Platform
  installer normally arranges this; see the project root `AGENTS.md`
  for the canonical install paths and how to fix `PATH` if needed.

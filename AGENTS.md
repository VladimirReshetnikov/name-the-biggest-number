# Agent Notes

`CLAUDE.md` in this repo is a symbolic link to `AGENTS.md`, so Claude
Code, OpenAI Codex, and any other agent that picks up either filename
reads the same content. If you edit one, you are editing both. On
Windows, the symlink is a real NTFS symlink (created with `mklink
CLAUDE.md AGENTS.md` and recorded in git as mode 120000). If a fresh
clone on Windows checks the file out as a plain text file containing
the string `AGENTS.md`, the local git config has symlink support
disabled — fix it with:

```powershell
git config core.symlinks true
git checkout -- CLAUDE.md
```

(Developer Mode or Administrator privileges are required for the
checkout to materialize as a real symlink on Windows.)

## Session Startup

- When starting a new conversation/session in this repo, review recent
  git history before doing substantive work. Do not stop at commit
  summaries: inspect the actual changes as well (for example with
  `git log --stat --patch -5` or another suitably detailed command).

## Git / Branch Conventions

- The default working branch is `ideas`. All next-contender brainstorm
  work, sandbox files, and `IDEAS.md` revisions go on this branch.
- Push `ideas` to `origin/ideas` only. `origin` is the user's fork at
  <https://github.com/VladimirReshetnikov/name-the-biggest-number.git>.
- At the end of each task, if any changes were made in this repo, commit
  them and push the current branch to `origin` without waiting for an
  explicit commit/push request.
- **Never** push to `upstream`
  (<https://github.com/codyroux/name-the-biggest-number.git>). It is the
  original maintainer's repository; the local clone has it configured
  only so we can pull updates.
- **Never** merge `ideas` (or any experiment branch) into `master`.
  `master` is treated as read-only on this fork; it tracks upstream so
  we can rebase/cherry-pick if needed.
- **Do not open pull requests.** Both inside the fork and against
  upstream. The brainstorm flow is push-to-`ideas` and iterate;
  promotion to a real contender PR will be a separate, explicit step
  the user initiates.
- Additional branches for experiments are fine. Push them to `origin`
  only, with descriptive names (e.g. `experiment-system-f`,
  `sandbox-bar-recursion`). Same rules: no PRs, no merges into
  `master`, no pushes to `upstream`.

## Next-Contender Ideas

- Use `IDEAS.md` for brainstorming and subsequent discussion of possible next
  contenders.
- Keep substantial design sketches, proof strategies, and tradeoff notes there
  so the thread of thought survives across future agent sessions.
- The usual work mode in this repository is an ongoing relay among
  different AI agents, often from different vendors and model families,
  taking turns to explore ideas, brainstorm, experiment, test approaches,
  and record observations. Treat each session as part of that shared
  research notebook, with the overall goal of producing the best next
  contender for "the biggest number ever named".
- Brainstorming sessions are the default mode for next-contender work. When
  asked to "elaborate on the currently proposed approach and/or propose a
  better one (or several)", treat it as exploratory. Multiple alternatives are
  welcome; do not converge prematurely. Record tradeoffs and dead ends, not
  just final picks.
- Experiment in Coq when it helps. Stand up scratch files in
  `sandbox/` (e.g. `sandbox/foo.v`, `sandbox/experiment_bar.v`) to
  try ideas, compute small instances, and verify that proposed
  primitives actually compile and reduce. Treat these as artifacts to
  commit alongside the prose in `IDEAS.md` so future agents can pick
  up the thread mechanically rather than re-deriving everything.
- Keep experimental files in `sandbox/`, separate from the contender
  chain at the repo root. The official `Contender.v` follows the rules
  in `README.md`; sandbox files do not need to and are free to use
  axioms, `Admitted`, slow tactics, etc. while ideas are in flux.
- When an experimental file becomes a serious candidate, the next step is a
  cleanup pass to make it axiom-free and within the 15s/60s budgets stated in
  `README.md` before merging into `Contender.v`.

## Current Game Plan

(Updated 2026-04-30, second relay session.)

The existing sandbox candidates beat `Contender.contender_5` mechanically
and axiom-free, but submitting any of them to upstream is **premature**.
Most of them reuse `Contender.largest_STLCNatRec_nat_of_depth` (the
exact engine that defines `contender_5`) as an *oracle* in a slightly
larger reflective language, which is borderline-violating the upstream
`README.md` rule:

> Hope this doesn't really need to be said, but don't use `contender_N`
> as a definition when defining `contender_N+1`, it's just lazy. Try to
> defeat the previous contender by a large margin, if you can.

The user has explicitly ruled the current sandbox candidates "too close
to violating the don't-be-lazy rule" for an upstream PR.  So:

- **Do not open a submission PR.**  Reaffirms the standing rule under
  Git / Branch Conventions above; adds the further rule that we do not
  even *plan* a specific submission until we have a candidate the user
  approves as clean.
- **Aim for `contender_6` candidates whose definitions do not reference
  `largest_STLCNatRec_nat_of_depth`** (or anything definitionally tied
  to it: `interp_term`, `termsUpTo`, `largest_of_depth`, etc.).  A
  *fresh engine* is the goal -- a number whose Coq definition uses a
  growth mechanism that is not just "depth-bounded max over System T
  terms, possibly wrapped".
- **The Brouwer-FGH track (`sandbox/Brouwer.v`) is the cleanest fresh
  engine we have right now**, but its connector to `contender_5` is
  open.  Specifically, proving `BigGrow N > Contender.contender_5` for
  some specific `N` requires bounding the eval of any closed depth-≤42
  STLC+NatRec term by `f_alpha(42)` for some `alpha < epsilon_0`.  That
  is the proof-theoretic ordinal of System T -- a known, true theorem,
  but not a one-line Coq lemma.
- **Existing oracle-based sandboxes stay as research artifacts.**
  `ReflectTowerNoAx`, `ReflectRTowerSmall`, `ReflectRTowerComputed`,
  `ReflectRTower3`, `BigGrowPrevMax`, and `BigGrowRTower` document
  mechanical patterns and small lemmas (`R_tower_S_d_mono`,
  `BigGrow_ge`, `BigGrow_gt_S`, `maxBy_subset`) that any future fresh-
  engine candidate may reuse.  They should *not* be ported to
  `Contender.v` as-is.

Concrete brainstorming directions we want to push next, ordered roughly
by how clean a `contender_6` they would produce:

1. **Connector lemma for Brouwer-FGH.**  Prove (or even partially
   prove) `eval t <= f_alpha(d)` for closed STLC+NatRec terms `t` of
   depth `d`, for some specific schema of `alpha < epsilon_0`.  Once
   any concrete bound is in place, `Definition contender_6 := BigGrow
   N` for a sufficiently large `N` is the cleanest possible submission
   -- the engine (Brouwer-ordinal FGH at `epsilon_0`) is wholly
   disjoint from `contender_5`'s machinery.
2. **Higher Brouwer ordinals.**  Define `epsilon_1`, `epsilon_omega`,
   `zeta_0`, `Gamma_0`, Bachmann-Howard, etc. as Brouwer terms (the
   `Blim : (nat -> Brouwer) -> Brouwer` constructor handles any
   countable ordinal with a fundamental sequence).  Each gives a
   stronger `BigGrow := FGH ord` for free.  Strengthens (1) when the
   connector lemma is in place; on its own, an aesthetic win and a
   stress test of the Brouwer formulation.
3. **Veblen functions (φ_β).**  φ_0(α) = ω^α, φ_{β+1}(α) the α-th
   common fixed point of φ_β.  Directly definable on Brouwer ordinals.
   Goes through `Gamma_0` (the small Veblen ordinal) cleanly.
4. **Approach B (System F).**  The repo already ships `System_F.v`
   with a normalization proof.  A System-F-based contender would use
   impredicative polymorphism, a genuinely orthogonal axis to System
   T's ordinal-indexed primitive recursion.  Heavier engineering than
   the Brouwer track; depth-bounded enumeration over both type and
   term binders is fiddlier.
5. **Approach F (Goodstein / hydra).**  Define the Goodstein function
   in Coq via Brouwer-ordinal descent, or the Kirby-Paris hydra
   game.  Both are canonical `f_{epsilon_0}`-strength examples and
   would be a different engine from any reflection-based candidate.
   Brouwer ordinals make termination easy; the encoding of hereditary
   base-`n` representations is the real work.
6. **Friedman's TREE / SCG / WORM.**  Beyond `f_{epsilon_0}` strength;
   Π^1_1-CA_0-flavoured.  Substantial encoding cost.
7. **Bar recursion (Spector).**  Different recursion principle, HA²
   strength.  Heavier still.
8. **Genuinely different evaluation models.**  Term graphs,
   interaction nets, abstract reduction systems with explicit
   termination invariants.  Open-ended but possibly fruitful for
   "fresh engine" contenders.

When extending the sandbox, prefer files that explore the above
directions over files that combine more oracles into the existing
reflection track.  In particular, "+1 step on top of the previous
oracle-based contender" patterns are now considered saturated: writing
yet another `contender_X = BigGrow (S contender_Y)` style file is not
a productive use of session bandwidth.

When in doubt about whether a proposed candidate is "clean enough",
write the candidate's `Definition` in prose first and check: does its
reading mention `largest_STLCNatRec_nat_of_depth`, `R_tower`, or any
sandbox alias of those?  If yes, it is still oracle-based, and is
useful as a research artifact but not as a submission target.

## Local Windows Environment

This is a Windows 11 box. Beyond the Coq/Rocq toolchain (next section),
the following CLI tools are available in fresh shells. Most are on
`PATH` after a shell restart; if not, the indicated install path can
be prepended manually.

### Search and indexing

- `rg` (ripgrep) — fast repository text search; `rg --files` for fast
  file listing.
- `ugrep` / `ug` — ripgrep-compatible search with extra regex,
  archive, and compressed-file support; v7.7.0 via `winget`.
- `es.exe` — voidtools Everything CLI; near-instant filename / path
  lookup across the entire local Windows footprint.
- `fd` — ergonomic filename / path traversal inside a tree.

### Data inspection

- `jq` — JSON inspection and filtering.
- `sqlite3` — ad-hoc SQLite inspection and queries.

### Source / repo

- `gh` — GitHub CLI for repos, PRs, and Actions workflows. Note that
  the project's "no PRs" rule (above) still applies; `gh` is for
  reading and for running workflows.

### Languages and runtimes

- `pwsh` — machine-wide PowerShell 7 at
  `C:\Program Files\PowerShell\7\pwsh.exe`. Use `winget upgrade
  Microsoft.PowerShell` (or `winget install Microsoft.PowerShell`) to
  refresh.
- `python` — `pyenv-win` is installed at `C:\Users\vresh\.pyenv\` and
  has versions `3.9.0`, `3.9.9`, `3.12.0`, `3.13.13` available; its
  shim lives at `C:\Users\vresh\.pyenv\pyenv-win\shims\python.bat`.
  However, the bare `python` command currently resolves to
  `C:\Users\vresh\AppData\Local\Microsoft\WindowsApps\python.exe`
  (Microsoft `pythoncore` `3.14.4`), which appears earlier on `PATH`
  than the pyenv shim. To use a pyenv-managed Python, either invoke
  the shim explicitly (`& "$env:USERPROFILE\.pyenv\pyenv-win\shims\python.bat"`),
  set `PYENV_VERSION`, or reorder `PATH` so the pyenv `shims` directory
  precedes `WindowsApps`.
- `fnm` (Fast Node Manager) at
  `C:\Users\vresh\AppData\Local\Microsoft\WinGet\Links\fnm.exe`.
  Default Node is `v25.9.0` (Current) with npm `11.12.1` under
  `C:\Users\vresh\AppData\Roaming\fnm\node-versions\v25.9.0\installation`.
- `uv` (Astral) at `C:\Users\vresh\.local\bin\uv.exe`, with
  `uvx.exe` and `uvw.exe` siblings. `uv self update` upgrades it in
  place.

### Document tooling

- `pandoc` 3.9.0.2 (`winget` package `JohnMacFarlane.Pandoc`) at
  `C:\Users\vresh\AppData\Local\Pandoc\pandoc.exe`. If a fresh shell
  cannot find it, prepend `C:\Users\vresh\AppData\Local\Pandoc` to
  `PATH`.
- `lualatex` via MiKTeX 26.2 (`winget` package `MiKTeX.MiKTeX`) at
  `C:\Users\vresh\AppData\Local\Programs\MiKTeX\miktex\bin\x64`.
  Package auto-install is enabled; current shells may need that bin
  directory prepended to `PATH`.

### Agent / AI

- `claude` (Anthropic Claude Code) at
  `C:\Users\vresh\.local\bin\claude.exe`. Git Bash is pinned via
  `CLAUDE_CODE_GIT_BASH_PATH`. API-key auth is bridged from the
  `ANTHROPIC_KEY` user env var through
  `C:\Users\vresh\.claude\settings.json` (`apiKeyHelper`).

### Package management

- `winget`, `choco`, and `refreshenv` for local Windows package
  management and shell environment refresh.

### Installing additional tools

You are authorized to install tools via `winget`, `choco`, or any
other reasonable installer when a tool is necessary or materially
helpful for the assigned task. If an installation fails, requires
unusual manual intervention, or leaves the tool unusable, **stop and
ask the user** rather than silently giving up or working around it.

When you install something generally useful (not a one-off), add a
bullet to the relevant subsection above (or to `Local Coq/Rocq
Toolchain` if it's prover-related), with the install method, the
canonical path, and any environment-refresh quirks. The next agent
session should be able to discover the tool from this file alone.

## Local Coq/Rocq Toolchain

- `rocq/` in this repository is a source snapshot of the upstream
  Rocq/Coq prover repository at <https://github.com/rocq-prover/rocq>.
  Treat it as local reference material for prover implementation
  details; it is separate from the installed Rocq Platform toolchain
  described below.
- Coq is installed through the Rocq Platform winget package:
  - Package ID: `Coq.CoqPlatform`
  - Platform version: `2025.08.2`
  - Prover version: `The Rocq Prover, version 9.0.1`
  - OCaml version reported by the prover: `4.14.2`
- Installation root:
  - `C:\Rocq-Platform~9.0~2025.08`
- Binary directory:
  - `C:\Rocq-Platform~9.0~2025.08\bin`
  - Contains `coqc.exe`, `coqtop.exe`, `coqchk.exe`, `coq_makefile.exe`,
    `rocq.exe`, and related tools.
- Library directory:
  - `C:\Rocq-Platform~9.0~2025.08\lib\coq`
- The user environment is configured so new shells should have:
  - `PATH` including `C:\Rocq-Platform~9.0~2025.08\bin`
  - `ROCQLIB=C:\Rocq-Platform~9.0~2025.08\lib\coq`
- If a current shell does not see the toolchain yet, prepend the binary
  directory and set `ROCQLIB` for that shell before running Coq:

```powershell
$env:PATH = 'C:\Rocq-Platform~9.0~2025.08\bin;' + $env:PATH
$env:ROCQLIB = 'C:\Rocq-Platform~9.0~2025.08\lib\coq'
```

## Existing Sandbox Files

These are throwaway-but-committed experiment files under `sandbox/`.
They are intentionally not part of the contender chain; they exist so
the brainstorming thread does not get lost between sessions.

- `sandbox/baseline.v` — probes `largest_STLCNatRec_nat_of_depth` at
  small depths (1–4) and prints `term_depth ack_reified` /
  `term_depth contender_4''_reified`. Useful for "how much depth
  budget does X really cost?" questions.
- `sandbox/FGH.v` — Cantor Normal Form ordinals < epsilon_0,
  fundamental sequence, fast-growing hierarchy with a fuel
  parameter. Computes small FGH values via `vm_compute`.
- `sandbox/L6.v` — structural sketch of L6 = STLC+NatRec extended
  with `tpOrd`, `tOZ`, `tOCons`, `tFGH`. Compiles, evaluates a couple
  of toy terms, prints their `term_depth`. Does not include the
  depth-bounded enumeration, the embedding from STLC+NatRec, or the
  Grow lemma — those live in `IDEAS.md` as text for now.
- `sandbox/ReflectPrev.v` — one-level reflective extension of
  STLC+NatRec with `tPrevMax : Nat -> Nat` interpreted as
  `largest_STLCNatRec_nat_of_depth`. Rebuilds depth-bounded
  enumeration for the extended language and proves
  `contender_5_lt_reflect_6`; compile from repo root with
  `coqc -Q . "" sandbox\ReflectPrev.v` after `Contender.vo` exists.
- `sandbox/ReflectTower.v` — generalisation of `ReflectPrev.v` to a
  parameterized previous-max oracle plus a structural reflection tower
  `R_tower : nat -> nat -> nat`. Proves
  `Contender.contender_5 < R_tower 100 342` (called
  `contender_reflect_tower_7` in-file). Uses `Opaque` pragmas on
  `Contender.largest_STLCNatRec_nat_of_depth`, `largest_reflect_nat_of_depth`,
  `eval`, `termsUpTo`, and `maxBy` to keep the kernel from
  unfolding the depth-bounded enumeration during conversion. Compile
  with `coqc -Q . "" sandbox\ReflectTower.v` after `Contender.vo`.
  Imports `FunctionalExtensionality` for the `cast_same` reduction
  lemma; `Print Assumptions` reports
  `functional_extensionality_dep` only.
- `sandbox/ReflectRTower.v` — second-order reflection (Approach D.2):
  defines `L_RT = STLC+NatRec+tRTower` where
  `tRTower : Nat -> Nat -> Nat` is interpreted as
  `sandbox.ReflectTower.ReflectTower.R_tower`. Rebuilds the depth-bounded
  maximum in `L_RT` and proves
  `Contender.contender_5 < contender_reflect_rtower_8` (with a witness
  `S (tRTower 100 342)` at `term_depth = 345`). Uses `Opaque` on
  `eval` / `maxBy` / the enumerator before applying the maxBy lower-bound
  lemma, to keep the kernel from running the depth-bounded search during
  conversion. Compile with `coqc -Q . "" sandbox\ReflectRTower.v` after
  `sandbox\ReflectTower.v` has been built.
- `sandbox/ReflectTowerNoAx.v` — axiom-free variant of `ReflectTower.v`
  (Track 1 prep for promotion).  Same end-state theorem
  `Contender.contender_5 < R_tower 100 342`, but
  `FunctionalExtensionality` is no longer imported and `Print
  Assumptions contender_5_lt_reflect_tower_7` reports a closed global
  context.  Achieved by restricting `interp_tApp` to `tpNat`-typed
  arguments (where `cast tpNat = id` is definitional) and dropping
  `interp_tLam` / `cast_impl_same`, both of which are unused for the
  witness chain.  Also exposes [d]-monotonicity of
  `largest_reflect_nat_of_depth` and `R_tower (S k)` (Phase 2
  prerequisite for IDEAS.md Approach D.2).  Compile with
  `coqc -Q . "" sandbox\ReflectTowerNoAx.v` after `Contender.vo`.
- `sandbox/ReflectRTowerSmall.v` — small-witness, axiom-free variant of
  `ReflectRTower.v` (Approach D.2, "Phase 1" of the computed-K/D
  refinement).  Imports `sandbox.ReflectTowerNoAx` and uses the
  smallest pair `(K, D) = (1, 45)` from `R_tower_step 0 42`, giving a
  witness term `S (tRTower 1 45)` at `term_depth = 48` instead of 345.
  `Print Assumptions contender_5_lt_reflect_rtower_small` reports a
  closed global context.  Compile with
  `coqc -Q . "" sandbox\ReflectRTowerSmall.v` after
  `sandbox\ReflectTowerNoAx.vo` has been built.
- `sandbox/Brouwer.v` — Brouwer ordinal notations and the fast-growing
  / Hardy hierarchies up to and through `epsilon_0` (Approach A).
  Inductive type `Brouwer = Bz | Bsucc Brouwer | Blim (nat -> Brouwer)`
  bakes the fundamental sequence into limit-ordinal data, so `FGH`,
  `Hardy`, `Badd`, `Bmul`, `omega_pow`, and `epsilon_0` are all plain
  `Fixpoint`s -- the Coq W-type guard accepts the
  `Hardy (f n) n` recursive call inside the `Blim f` case as a
  structural subterm.  Defines
  `BigGrow := FGH epsilon_0 : nat -> nat` and reports a closed global
  context for it.  This bypasses the well-foundedness blocker that
  the CNF-based `sandbox/FGH.v` would have to solve.  Compile with
  `coqc -Q . "" sandbox\Brouwer.v`; standalone, ~1 s.
- `sandbox/BigGrowPrevMax.v` — BigGrow + prevMax diagonalization (hybrid
  of Approach E and the reflection-oracle pattern): extends the
  `ReflectTowerNoAx`-style language with a primitive
  `tBigGrow : Nat -> Nat` interpreted as `sandbox.Brouwer.BigGrow`
  (i.e. `FGH epsilon_0`). Proves the generic strict step
  `prevMax d < largest_BGPrev_nat_of_depth prevMax (d + 4)` via the
  witness term `tBigGrow (S (tPrevMax d))`, and instantiates it at
  `d = 42` to get `Contender.contender_5 < contender_bigGrowPrev` with a
  witness at `term_depth = 46`. `Print Assumptions` reports a closed
  global context. Compile with `coqc -Q . "" sandbox\BigGrowPrevMax.v`
  after `Contender.vo` and `sandbox\Brouwer.vo`.
- `sandbox/BigGrowRTower.v` — composes the Brouwer-FGH and reflection
  axes.  Plugs `R_tower 1` in as the `prevMax` oracle to the existing
  `BigGrowPrevMax.largest_BGPrev_nat_of_depth`, and also records a
  pure-composition variant `BigGrow (S (R_tower 1 45))` and a stacked
  variant `BigGrow (S contender_BG_RT_layered)`.  All three are
  axiom-free (`Print Assumptions` reports closed global contexts) and
  beat `contender_5` via the chain `contender_5 < R_tower 1 45 <
  contender_BG_RT_layered < contender_BG_RT_stacked` plus
  `contender_5 < contender_BG_RT_simple` via `BigGrow_ge`.  Compile
  with `coqc -Q . "" sandbox\BigGrowRTower.v` after
  `sandbox\BigGrowPrevMax.vo`.
- `sandbox/BrouwerHigh.v` — extends `sandbox/Brouwer.v` with named
  Brouwer terms past `epsilon_0`: `next_epsilon`, `epsilon_at` (any
  finite `epsilon_k`), `epsilon_omega`, `phi_2`, `zeta_0`, and
  `Gamma_0` (the Feferman-Schutte ordinal).  Companion `nat -> nat`
  candidate engines `BigGrow_eN`, `BigGrow_e_omega`, `BigGrow_zeta_0`,
  `BigGrow_Gamma_0` are FGH at the corresponding ordinals.  All
  axiom-free; nine `Print Assumptions` lines all report closed global
  contexts.  Useful as alternative engines for any future fresh-engine
  `contender_6` once the connector lemma (IDEAS.md Approach J) is in
  place.  Compile with `coqc -Q . "" sandbox\BrouwerHigh.v` after
  `sandbox\Brouwer.vo`.
- `sandbox/ReflectRTowerComputed.v` — computed-argument D.2 refinement
  ("Phase 2").  Imports `sandbox.ReflectRTowerSmall` and defines
  offset-aware NatRec arithmetic combinators (`double_at`, `pow2_at`)
  for the reversed de Bruijn-level convention.  Proves
  `eval RTower (pow2_at 0 (natlit 6)) = 64` and
  `eval RTower (pow2_at 0 (natlit 1)) = 2`.  Records the D-only witness
  `S (tRTower 1 (pow2 6))` at `term_depth = 19`, then proves the
  stronger computed-K/D theorem with
  `S (tRTower (pow2 1) (pow2 6))` at `term_depth = 20`, using
  `R_tower_step 1 45` and `R_tower_S_d_mono 1 48 64`.
  `Print Assumptions` reports a closed global context; compile with
  `coqc -Q . "" sandbox\ReflectRTowerComputed.v` after
  `sandbox\ReflectRTowerSmall.vo`.
- `sandbox/ReflectRTower3.v` — Approach D.3 ("meta-reflection"):
  takes the D.2 depth-bounded maximum itself as the oracle
  `prevMax2 d := largest_RT_nat_of_depth RTower d`, then applies the
  one-step `ReflectTowerNoAx` witness trick to get a strict improvement
  `contender_reflect_rtower_computed < contender_reflect_rtower3`, where
  `contender_reflect_rtower3 = largest_reflect_nat_of_depth prevMax2 23`.
  Also proves `Contender.contender_5 < contender_reflect_rtower3` by
  transitivity.  Repeats the `Opaque` barrier on the D.2 max/search
  machinery so a definitional `change` does not trigger kernel
  conversion to run the depth-bounded enumeration.  Compile with
  `coqc -Q . "" sandbox\ReflectRTower3.v` after
  `sandbox\ReflectRTowerComputed.vo`.

When extending these or adding new ones, drop them in `sandbox/` so
they are visually distinguished from the contender chain. They do not
need to satisfy `Contender.v`'s 15 s / 60 s budgets or the no-axioms
rule until they are being prepared for promotion.

## Verification Commands

To verify the current contender file from this repository root:

```powershell
coqc Contender.v
coqchk Contender
```

`Contender.v` was verified successfully on this machine with Rocq 9.0.1.
Compilation emits Rocq 9 compatibility warnings for unqualified Stdlib imports
and a large-`nat` literal warning, but the proof checks and `coqchk Contender`
succeeds.

Sandbox files compile via `coqc sandbox/<name>.v`. Standalone ones
(`sandbox/FGH.v`, `sandbox/L6.v`) need no extra flags. Files that
`Require Contender.` (`sandbox/baseline.v`) need the parent on the
load path — compile from repo root with

```powershell
coqc -Q . "" sandbox\baseline.v
```

after `coqc Contender.v` has produced `Contender.vo`. All sandbox
files emit Rocq 9 deprecation warnings about unqualified Stdlib
imports — ignorable.

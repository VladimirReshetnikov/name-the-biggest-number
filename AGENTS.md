# Agent Notes

## Next-Contender Ideas

- Use `IDEAS.md` for brainstorming and subsequent discussion of possible next
  contenders.
- Keep substantial design sketches, proof strategies, and tradeoff notes there
  so the thread of thought survives across future agent sessions.
- Brainstorming sessions are the default mode for next-contender work. When
  asked to "elaborate on the currently proposed approach and/or propose a
  better one (or several)", treat it as exploratory. Multiple alternatives are
  welcome; do not converge prematurely. Record tradeoffs and dead ends, not
  just final picks.
- Experiment in Coq when it helps. Stand up scratch files (e.g.
  `Sandbox_*.v`, `Experiment_*.v`) to try ideas, compute small instances,
  verify that proposed primitives actually compile and reduce. Treat these
  as artifacts to commit alongside the prose in `IDEAS.md` so future agents
  can pick up the thread mechanically rather than re-deriving everything.
- Keep experimental files separate from `Contender.v`. The official contender
  file follows the rules in `README.md`; sandbox files do not need to and are
  free to use axioms, `Admitted`, slow tactics, etc. while ideas are in flux.
- When an experimental file becomes a serious candidate, the next step is a
  cleanup pass to make it axiom-free and within the 15s/60s budgets stated in
  `README.md` before merging into `Contender.v`.

## Local Coq/Rocq Toolchain

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

These are throwaway-but-committed experiment files. They are
intentionally not part of the contender chain; they exist so the
brainstorming thread does not get lost between sessions.

- `Sandbox_baseline.v` — probes `largest_STLCNatRec_nat_of_depth` at
  small depths (1–4) and prints `term_depth ack_reified` /
  `term_depth contender_4''_reified`. Useful for "how much depth
  budget does X really cost?" questions.
- `Sandbox_FGH.v` — Cantor Normal Form ordinals < epsilon_0,
  fundamental sequence, fast-growing hierarchy with a fuel
  parameter. Computes small FGH values via `vm_compute`.
- `Sandbox_L6.v` — structural sketch of L6 = STLC+NatRec extended
  with `tpOrd`, `tOZ`, `tOCons`, `tFGH`. Compiles, evaluates a couple
  of toy terms, prints their `term_depth`. Does not include the
  depth-bounded enumeration, the embedding from STLC+NatRec, or the
  Grow lemma — those live in `IDEAS.md` as text for now.

When extending these or adding new ones, prefer the `Sandbox_*.v`
prefix so they are visually distinguished from the contender chain.
They do not need to satisfy `Contender.v`'s 15 s / 60 s budgets or
the no-axioms rule until they are being prepared for promotion.

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

Sandbox files compile via `coqc Sandbox_*.v`. They depend on
`Contender.vo` (compiled by the command above) only when they
explicitly `Require Contender.`. They emit Rocq 9 deprecation warnings
about unqualified Stdlib imports — ignorable.

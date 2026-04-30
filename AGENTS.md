# Agent Notes

## Next-Contender Ideas

- Use `IDEAS.md` for brainstorming and subsequent discussion of possible next
  contenders.
- Keep substantial design sketches, proof strategies, and tradeoff notes there
  so the thread of thought survives across future agent sessions.

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

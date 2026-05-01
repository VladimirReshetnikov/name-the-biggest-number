# Ideas for Beating the Current Contender

## Where we are

The current contender is

```coq
Definition contender_5 : nat := largest_STLCNatRec_nat_of_depth 42.
```

which is the largest natural number produced by any closed STLC+NatRec term
of `term_depth` at most 42. STLC+NatRec is essentially Gödel's System T:
its `Nat -> Nat` definables are exactly the provably total recursive
functions of Peano Arithmetic, bounded uniformly by `f_alpha` for some
`alpha < epsilon_0` in the fast-growing hierarchy.

Beating just the *value* (e.g. by using a slightly larger Ackermann) is no
longer interesting. What we want is to beat the *method*: produce a new
contender that subsumes STLC+NatRec by structural embedding and then
applies a strictly stronger total construct.

Empirically (from `sandbox/baseline.v`):

| `d`  | `length (termsUpTo d)` | `largest_STLCNatRec_nat_of_depth d` |
|------|-----------------------:|------------------------------------:|
| 1    | 2                      | 0                                   |
| 2    | 10                     | 1                                   |
| 3    | 146                    | 2                                   |
| 4    | 24 976                 | 3                                   |
| ...  | ...                    | (explodes)                          |
| 42   | infeasible to enumerate | `contender_5`                      |

Reified depths of the existing witnesses:

* `term_depth ack_reified = 26`
* `term_depth contender_4''_reified = 30`

So at depth 42 there is roughly 12 levels of slack on top of `ack 5 42 10002`.
Plenty of room for the enumeration to produce something far past `ack`,
but everything in the budget is still bounded by some `f_alpha` with
`alpha < epsilon_0`.

### 2026-04-30 sandbox update

New experiment: `sandbox/ReflectPrev.v`.

It defines a one-level reflective extension of STLC+NatRec with a primitive

```coq
tPrevMax : Nat -> Nat
```

interpreted as `largest_STLCNatRec_nat_of_depth`. The file rebuilds the
depth-bounded term enumeration for this extended language and proves:

```coq
Theorem contender_5_lt_reflect_6 :
  Contender.contender_5 < contender_reflect_6.
```

where

```coq
Definition contender_reflect_6 : nat := largest_reflect_nat_of_depth 45.
```

The witness is the internal term

```coq
S (tPrevMax 42)
```

with `term_depth = 45`. The proof compiles with:

```powershell
coqc -Q . "" sandbox\ReflectPrev.v
```

and `Print Assumptions contender_5_lt_reflect_6` reports a closed global
context. This does not settle whether reflection is aesthetically acceptable
for the contest, but it turns Approach D from a handwave into a mechanically
available fallback.

### 2026-04-30 sandbox update — stratified reflection tower

Follow-up to ReflectPrev: `sandbox/ReflectTower.v`.

The single-level reflection of `ReflectPrev.v` is generalized into the
parameterized tower called for in Approach D.1 below. The reflective
extension of STLC+NatRec is parameterized over an arbitrary previous-max
oracle:

```coq
Section Reflect.
Context (prevMax : nat -> nat).
... STLC+NatRec + tPrevMax (interpreted as prevMax) ...
Definition largest_reflect_nat_of_depth : nat -> nat.
End Reflect.
```

Then the tower is a structural recursion on the level:

```coq
Fixpoint R_tower (k : nat) : nat -> nat :=
  match k with
  | 0    => Contender.largest_STLCNatRec_nat_of_depth
  | S k' => largest_reflect_nat_of_depth (R_tower k')
  end.
```

A single uniform witness term

```coq
witness_for d := tApp tS (tApp tPrevMax (natlit d))
```

has `term_depth = d + 3` and evaluates (in any level-(k+1) language with
`prevMax := R_tower k`) to `S (R_tower k d)`. This gives the level-step
lemma

```coq
Lemma R_tower_step : forall k d,
  R_tower k d < R_tower (S k) (S (S (S d))).
```

which iterates to

```coq
Lemma R_tower_chain : forall n,
  R_tower 0 42 < R_tower (S n) (3 * (S n) + 42).
```

and finally

```coq
Definition contender_reflect_tower_7 : nat := R_tower 100 342.

Theorem contender_5_lt_reflect_tower_7 :
  Contender.contender_5 < contender_reflect_tower_7.
```

The file compiles in ~3.5 s on this machine and `coqchk` accepts the
resulting module. `Print Assumptions` reports only
`functional_extensionality_dep`, used by the standard reduction-lemma
machinery for the typed evaluator (the same axiom Contender.v's reification
helpers use; a no-axioms refactor is an open cleanup task before promotion).

#### Engineering note: do not let the kernel evaluate `contender_5`

The first attempts to compile this file timed out at multiple minutes. The
cause was Coq's kernel conversion check trying to fully reduce
`R_tower 100 342` (and, via the universally-quantified `R_tower_step` lemma,
intermediate values of the form `R_tower (S k) D`) into normal form. Each
such reduction unfolds `largest_reflect_nat_of_depth (...) D` to the
`maxBy ... (termsUpTo D)` enumeration, which is exactly the contender's own
exponentially-large search.

The fix in the sandbox is to make the relevant constants opaque *after*
their structural lemmas are proven:

```coq
Opaque Contender.largest_STLCNatRec_nat_of_depth.
...
Lemma R_tower_step : ... .  (* needs the unfolding, proven first *)
Opaque largest_reflect_nat_of_depth.
Opaque eval.
Opaque termsUpTo.
Opaque maxBy.
Lemma R_tower_chain : ... .   (* now safe to apply at fixed depth *)
Theorem contender_5_lt_reflect_tower_7 : ... .
```

Lesson generalises: any future contender that names a depth-bounded maximum
inside its own definition has the same trap. Promotion to `Contender.v`
should pick a structural shape that lets the kernel stay symbolic on
`largest_*_nat_of_depth D` for the depth `D` actually used in the bound.

#### Where this leaves the choice

The reflection tower is now a fully mechanical, axiom-free-modulo-FunExt
contender path. Two consequences:

* **Approach D.1 is no longer a handwave.** A concrete level-100 contender
  is proven `< R_tower 100 342`. The level number can be set arbitrarily;
  the chain proof is structurally recursive in `n` and does not depend on
  the value of `n` for tactic time.
* **The remaining open question is taste, not feasibility.** A staged
  reflection hierarchy is constructive, finite, and has no axioms beyond
  what Contender.v already uses. Whether the contest wants a contender
  whose definition mentions `largest_STLCNatRec_nat_of_depth` is a
  judgement call for the maintainer of the chain, not a technical
  blocker.

See the new "Approach D.2" section below for the natural follow-up: lifting
`R_tower` itself into a primitive of yet another reflective language.

### 2026-04-30 sandbox update — RTower as a primitive (Approach D.2)

New experiment: `sandbox/ReflectRTower.v`.

It defines a new object language `L_RT`:

* STLC + NatRec
* plus a primitive

```coq
tRTower : Nat -> Nat -> Nat
```

interpreted as the already-constructed reflection tower from
`sandbox/ReflectTower.v`:

```coq
sandbox.ReflectTower.ReflectTower.R_tower : nat -> nat -> nat.
```

Then it rebuilds the same depth-bounded max machinery in `L_RT`:

```coq
Definition largest_RT_nat_of_depth (d : nat) : nat := ...
```

and proves a one-shot bound beyond `contender_5` by exhibiting the internal
witness term

```coq
S (tRTower 100 342)
```

at (computed) `term_depth = 345`:

```coq
Definition contender_reflect_rtower_8 : nat := largest_RT_nat_of_depth 345.

Theorem contender_5_lt_reflect_rtower_8 :
  Contender.contender_5 < contender_reflect_rtower_8.
```

Engineering note: the file marks `eval` / `maxBy` (and the enumerator) `Opaque`
*before* applying the maxBy lower-bound lemma at the concrete depth 345,
otherwise Coq's conversion check tries to run the depth-bounded search.

This is still the “unary literal” version of D.2; see the D.2 section below
for why the interesting next refinement is to *compute* large `K`/`D` values
at small `term_depth`, and the caveat about de Bruijn levels / shifting when
reusing arithmetic combinators.

### 2026-04-30 sandbox update — Track 1 prep: axiom-free reflection tower

New experiment: `sandbox/ReflectTowerNoAx.v`.

This is a structural cleanup of `sandbox/ReflectTower.v` that removes the
dependency on `FunctionalExtensionality`.  In `ReflectTower.v` the axiom
flowed in through `cast_impl_same -> cast_same -> interp_tApp -> ...`,
contaminating both `R_tower_step` and the main theorem.  But the witness
chain we actually use only ever applies functions to `tpNat`-typed
arguments, and for those `cast tpNat a = a` is *definitional*: no
extensionality detour.

So `ReflectTowerNoAx.v` keeps the same syntax, the same evaluator, the
same Fixpoint definition of `R_tower`, and the same chain proof, but:

* removes the import of `FunctionalExtensionality`,
* drops the `cast_impl_same` / `cast_same` lemmas (they would still need
  FunExt and are unused),
* drops `interp_tLam` (also FunExt-bound, unused for the witness),
* replaces `interp_tApp` with a `tpNat`-restricted variant
  `interp_tApp_nat`, whose proof is a one-line `simpl; rewrite; reflexivity`.

End-state theorem is identical:

```coq
Theorem contender_5_lt_reflect_tower_7 :
  Contender.contender_5 < contender_reflect_tower_7.
```

with `contender_reflect_tower_7 := R_tower 100 342`, but now

```text
Print Assumptions contender_5_lt_reflect_tower_7.
  Closed under the global context.
```

`coqchk` accepts the module without complaint.  Compile time is
comparable to `ReflectTower.v` (~3 s on this machine) and the no-axioms
status is independent of how big the level/depth pair is — `R_tower 100
342` and `R_tower 1 45` both close under the global context.

This closes Track 1's "no-axioms cleanup" sub-step from the recommendations
section of this file.  Promotion of the reflection tower to `Contender.v`
is now mechanically blocked only by the contest-aesthetics judgement, not
by any technical / axiom debt.

### 2026-04-30 sandbox update — small-witness D.2 (depth 48)

New experiment: `sandbox/ReflectRTowerSmall.v`.

This is a sibling of `sandbox/ReflectRTower.v` (Approach D.2), with two
combined changes:

* It imports the axiom-free `sandbox.ReflectTowerNoAx` instead of
  `sandbox.ReflectTower`.  Combined with using only `tpNat`-typed casts
  in this file's own evaluator, the resulting D.2 contender is *fully
  axiom-free*: `Print Assumptions contender_5_lt_reflect_rtower_small`
  reports a closed global context.

* It uses the smallest `(K, D)` pair the `R_tower_step` lemma directly
  produces: `K = 1, D = 45`, so the witness term is

  ```coq
  Definition witness_rtower_small : term :=
    tApp tS (tApp (tApp tRTower (natlit 1)) (natlit 45)).
  ```

  with `term_depth = 48`.  This shrinks the depth budget from 345 to 48
  while still strictly beating `contender_5` (the chain only needs the
  base case `R_tower_step 0 42`, no escalation to K=100).

End-state theorem:

```coq
Definition contender_reflect_rtower_small : nat :=
  largest_RT_nat_of_depth RTower 48.

Theorem contender_5_lt_reflect_rtower_small :
  Contender.contender_5 < contender_reflect_rtower_small.
```

`Print Assumptions` and `coqchk` both pass cleanly.

This is the simplest "Phase 1" of the computed-K/D refinement noted in
the original D.2 sandbox: no new infrastructure, just the realization
that the chain lemma's smallest case already suffices.

Phase 1 also adds the two depth-monotonicity lemmas needed by Phase 2,
in `sandbox/ReflectTowerNoAx.v`:

```coq
Lemma largest_reflect_d_mono : forall prev d1 d2,
    d1 <= d2 ->
    largest_reflect_nat_of_depth prev d1
    <= largest_reflect_nat_of_depth prev d2.

Lemma R_tower_S_d_mono : forall k d1 d2,
    d1 <= d2 -> R_tower (S k) d1 <= R_tower (S k) d2.
```

(The level-0 case is deliberately skipped to keep
`Contender.largest_STLCNatRec_nat_of_depth` Opaque; only positive
levels are needed for Phase 2 and beyond.)

*Phase 2* — making `K` and/or `D` themselves *computed* via NatRec,
e.g. as powers of two or tetration — is now demonstrated in
`sandbox/ReflectRTowerComputed.v`: inline `pow2 6 = 64` for the `D`
argument, and inline `pow2 1 = 2` for the `K` argument.  The final
proof uses `R_tower_step 1 45` plus `R_tower_S_d_mono 1 48 64`.

### 2026-04-30 sandbox update — computed-K/D D.2 (depth 20)

New experiment: `sandbox/ReflectRTowerComputed.v`.

This is the promised Phase 2 refinement of the small-witness D.2 file.
First, instead of using the unary literal `45`, it computes a larger
depth argument internally:

```coq
Definition witness_rtower_pow2_6 : term :=
  tApp tS (tApp (tApp tRTower (natlit 1)) pow2_6_term).

Lemma eval_pow2_6_term :
  eval RTower pow2_6_term = 64.

Lemma eval_witness_rtower_pow2_6 :
  eval RTower witness_rtower_pow2_6 = S (RTower 1 64).
```

That D-only witness lands at depth 19.  The file then computes `K` as
well:

```coq
Lemma eval_pow2_1_term :
  eval RTower pow2_1_term = 2.

Definition witness_rtower_pow2_1_6 : term :=
  tApp tS (tApp (tApp tRTower pow2_1_term) pow2_6_term).

Lemma eval_witness_rtower_pow2_1_6 :
  eval RTower witness_rtower_pow2_1_6 = S (RTower 2 64).

Definition contender_reflect_rtower_computed : nat :=
  largest_RT_nat_of_depth RTower (term_depth witness_rtower_pow2_1_6).

Theorem contender_5_lt_reflect_rtower_computed :
  Contender.contender_5 < contender_reflect_rtower_computed.
```

The key engineering lesson is about the existing reversed de Bruijn
*level* convention.  A reusable lambda combinator is not intrinsically
closed under surrounding binders: if a template is evaluated with `c`
ambient variables, the next binder is variable `c`, and the next one is
`S c`.  The new file therefore defines arithmetic templates as
`step_succ_at c`, `double_at c`, `step_double_at c`, and `pow2_at c`.
That prevents the "closed" `double` / `pow2` templates from accidentally
capturing the caller's surrounding variables.

Concrete result:

```text
eval RTower pow2_6_term = 64
eval RTower pow2_1_term = 2
term_depth pow2_6_term = 17
term_depth witness_rtower_pow2_6 = 19
term_depth witness_rtower_pow2_1_6 = 20
Print Assumptions contender_5_lt_reflect_rtower_computed.
  Closed under the global context.
```

The proof compiles in under a second when its imported sandbox modules
are already built, and `coqchk -Q . "" sandbox.ReflectRTowerComputed`
accepts the module.  This closes the specific Phase 2 item, while also
leaving a useful reusable pattern for future computed arguments:
parameterize object-level combinator templates by ambient level count.

### 2026-04-30 sandbox update — Brouwer-ordinal FGH at epsilon_0 (Approach A, no Acc)

New experiment: `sandbox/Brouwer.v`.

This is a fresh axis of attack on Approach A.  The original Approach A
sandbox `sandbox/FGH.v` represents ordinals in Cantor Normal Form and
defines the fast-growing hierarchy with a fuel parameter, because
well-founded recursion on the canonical CNF ordering is the open
problem.  `sandbox/Brouwer.v` sidesteps that problem by switching to
*Brouwer ordinal notations*:

```coq
Inductive Brouwer : Type :=
| Bz   : Brouwer
| Bsucc: Brouwer -> Brouwer
| Blim : (nat -> Brouwer) -> Brouwer.
```

In this presentation each limit ordinal *carries* its fundamental
sequence as data, and Coq's W-type guard accepts pure structural
recursion on Brouwer ordinals: a recursive call on `f n` inside a
`Blim f` case is automatically a strict subterm.  No `Acc`, no `Fix`,
no fuel.

Concretely the file delivers:

```coq
Fixpoint Badd  : Brouwer -> Brouwer -> Brouwer.   (* alpha + beta *)
Fixpoint Bmul  : Brouwer -> Brouwer -> Brouwer.   (* alpha * beta *)
Fixpoint omega_pow : Brouwer -> Brouwer.          (* omega ^ alpha *)

Definition omega       : Brouwer := Blim nat_to_B.
Definition omega_omega : Brouwer := omega_pow omega.

Fixpoint omega_tower (n : nat) : Brouwer := ...     (* omega ^^ n *)
Definition epsilon_0   : Brouwer := Blim omega_tower.

Fixpoint FGH   : Brouwer -> nat -> nat.            (* fast-growing hierarchy *)
Fixpoint Hardy : Brouwer -> nat -> nat.            (* Hardy hierarchy *)

Definition BigGrow (n : nat) : nat := FGH epsilon_0 n.
```

`Print Assumptions FGH/Hardy/epsilon_0/BigGrow` all report a closed
global context.  `coqchk` accepts the module.  Compile time ~1 s on
this machine.  Sanity outputs match the FGH textbook:

```text
FGH (nat_to_B 0) 10 = 11    (* f_0(10) *)
FGH (nat_to_B 2) 4  = 64    (* f_2(4) *)
FGH (nat_to_B 3) 2  = 2048  (* f_3(2) *)
FGH omega 2         = 8     (* f_omega(2) = f_2(2) *)
Hardy omega 10      = 20    (* H_omega(n) = 2n *)
Hardy omega_omega 2 = 8     (* H_{omega^omega}(2) *)
```

(`FGH omega 3 = f_3(3) = f_2^3(3)` already has ~10^8 bits, well past
`vm_compute`'s reach -- definable but not displayable.)

What this opens up:

* **Approach A is no longer blocked on well-foundedness.**  The CNF
  formulation in `sandbox/FGH.v` was bottlenecked on proving
  `well_founded ord_lt`; switching to Brouwer notations skips that
  proof obligation entirely.  Anything we wanted to compute in the
  `f_alpha` / `H_alpha` style for `alpha` up to and slightly beyond
  epsilon_0 is now available as a plain Coq function.
* **Approach E shrinks to a one-line definition.**  Instead of
  hard-coding a single ordinal-indexed primitive by hand, just take
  `BigGrow := FGH epsilon_0` (or any other Brouwer ordinal you trust)
  and add `tBigGrow : tpNat -> tpNat` as a primitive in a new
  STLC+NatRec+tBigGrow language.  Witness `S (tApp tBigGrow (natlit
  42))` lands at `term_depth = 45` and evaluates to `S (BigGrow 42) =
  S (f_{epsilon_0}(42))`.

Open follow-up: prove `BigGrow 42 > Contender.contender_5`.  The mechanical
shape is the usual maxBy lower-bound -- a contender language with
`tBigGrow` plus the standard depth-bounded enumeration -- but the
strict-inequality step needs a meta-theorem that every closed
`STLC+NatRec` term of depth 42 has eval bounded by `f_alpha(42)` for some
`alpha < epsilon_0`.  That is essentially the proof-theoretic bound on
System T; it is true and well-known, but not a one-line Coq proof.

The file also records small structural lemmas (`FGH_Bsucc`,
`FGH_Blim`, `Nat_iter_FGH_Bz`, `FGH_one_eq`, plus the Hardy analogues)
that future contender work can build on without re-deriving the
unfolding.

### 2026-04-30 sandbox update — meta-reflection over `largest_RT_nat_of_depth` (Approach D.3)

New experiment: `sandbox/ReflectRTower3.v`.

This takes the D.2 language's depth-bounded maximum function itself as the
oracle for the one-step reflection language from `sandbox/ReflectTowerNoAx`:

```coq
Definition prevMax2 (d : nat) : nat :=
  sandbox.ReflectRTowerSmall.largest_RT_nat_of_depth sandbox.ReflectRTowerSmall.RTower d.

Definition depth_reflect_d0 : nat :=
  S (S (S sandbox.ReflectRTowerComputed.depth_rtower_pow2_1_6)).

Definition contender_reflect_rtower3 : nat :=
  sandbox.ReflectTowerNoAx.ReflectTowerNoAx.largest_reflect_nat_of_depth prevMax2 depth_reflect_d0.

Theorem contender_reflect_rtower_computed_lt_reflect_rtower3 :
  sandbox.ReflectRTowerComputed.contender_reflect_rtower_computed < contender_reflect_rtower3.
```

Because `depth_rtower_pow2_1_6` is definitionally 20, `depth_reflect_d0` is 23,
so this is a strict improvement over the computed-K/D D.2 max at a tiny
additional depth cost.

Engineering note: even the definitional rewrite that identifies
`contender_reflect_rtower_computed` with `prevMax2 depth_rtower_pow2_1_6`
can trigger kernel conversion to run the D.2 depth-bounded search unless the
search machinery is made `Opaque` in the D.3 file too. `ReflectRTower3.v`
therefore repeats the `Opaque` barrier for `largest_RT_nat_of_depth` and its
`eval` / `maxBy` / `termsUpTo` helpers before the `change ... with (prevMax2 ...)`
step.

## The general framework

Pick a new total object language `L6` with:

1. A type system at least as rich as STLC+NatRec.
2. Term enumeration up to a depth `d`.
3. A computable evaluator into `nat`.

Then define

```coq
Definition contender_6 : nat := largest_L6_nat_of_depth d.
```

and prove `contender_5 < contender_6` by:

* defining `embed_type` and `embed_term` from STLC+NatRec to `L6`,
* showing that `embed_term` preserves both `term_depth` (or shifts it by a
  fixed constant) and the evaluation result,
* exhibiting an `L6`-specific witness term `Grow (embed t*)` where `t*` is
  the unknown depth-≤42 STLC+NatRec witness for `contender_5`,
* proving `eval_L6 (Grow (embed t*)) > contender_5` and that the witness
  fits within the new depth budget.

The witness `t*` does not need to be named in the definition of
`contender_6`; it is conjured existentially via the maxBy lemmas (the
`maxBy_In` / `lowerbound_maxBy` combo already in `Contender.v`).

## Approach A — ordinal-indexed fast-growing hierarchy as a primitive

This is the approach already sketched in the previous version of
`IDEAS.md`. We elaborate it here with the data structures and tradeoffs
made concrete by `sandbox/FGH.v` and `sandbox/L6.v`.

### A.1 Cantor Normal Form ordinals

Use the inductive type

```coq
Inductive ord : Set :=
| oz    : ord
| ocons : ord -> ord -> ord.   (* ocons a b stands for omega^a + b *)
```

with the (non-enforced) CNF invariant `a >= leading_exponent(b)`. From
`sandbox/FGH.v` the canonical fundamental sequence and FGH compute as
expected at small inputs:

* `ord_fund_seq omega 5    = 5`
* `ord_fund_seq (omega*2) 3 = omega + 3`
* `ord_fund_seq (omega^2) 4 = omega * 4`
* `ord_fund_seq (omega^omega) 3 = omega^3`
* `f_2(4) = 64`, `f_2(6) = 384`, `f_3(2) = 2048`, `f_omega(2) = 8`

The CNF representation is compact:

* `ord_size omega = 5`,  `ord_height omega = 3`
* `ord_size (omega^omega) = 7`, `ord_height (omega^omega) = 4`
* `ord_size (omega↑↑5) = 13`,   `ord_height (omega↑↑5) = 7`
* `ord_size (omega↑↑10) = 23`,  `ord_height (omega↑↑10) = 12`

Since `epsilon_0 = sup_n omega↑↑n` and is *not* expressible in CNF, the
strongest `Grow` we can name in this representation is `f_{omega↑↑h}` for
a finite `h`. The total ordinal complexity grows linearly in `h`, so a
serious headroom (e.g. `h = 5` or `h = 10`) costs only a few extra
levels of `term_depth`.

### A.2 The L6 language

`sandbox/L6.v` shows the data types compile and evaluate. The
extension over STLC+NatRec is:

```coq
Inductive type :=
| tpNat : type
| tpOrd : type
| tpArr : type -> type -> type.

Inductive term :=
| tVar (x : nat)
| tLam (A B : type) (body : term)
| tApp (t1 t2 : term)
| tO | tS
| tNatRec (R : type)
| tOZ | tOCons | tFGH.
```

with the obvious typing:

```
tOZ    : tpOrd
tOCons : tpOrd -> tpOrd -> tpOrd
tFGH   : tpOrd -> tpNat -> tpNat
```

Sanity check from the L6 sandbox:

* `eval (tApp (tApp tFGH (encode 1)) (encode 3)) = 6` at term_depth 5.
* `eval (tApp (tApp tFGH omega) (encode 2)) = 8`   at term_depth 7.

So depth 7 in L6 already exceeds depth 4 in plain STLC+NatRec.

### A.3 Picking the budget

To reuse the existing maxBy witness machinery we need the depth budget
`d6` to satisfy

```
d6 >= max(term_depth_L6 (encode big_ord), term_depth_L6 (embed t*)) + 1
    = max(term_depth_L6 (encode big_ord), 42) + 1.
```

`omega↑↑5` encodes at term_depth ≈ 17 in L6, well below 42. Using
`d6 = 44` (the value the original IDEAS.md proposed) leaves comfortable
headroom and lets us pick a beefier ordinal.

The Grow witness is then morally

```coq
tApp (tApp tFGH (encode (omega_tower 5))) (embed t*)
```

and we get the strict domination

```coq
contender_6 >= f_{omega↑↑5}(contender_5) > contender_5.
```

### A.4 Proof obligations

In rough order:

1. Soundness of the L6 evaluator (mirror of `interp_term` in
   `Contender.v`, plus the new ord/FGH cases).
2. Termination of `FGH_total`. The simplest path is well-founded
   recursion on the lexicographic pair `(ord, nat)` or
   `(ord_size, nat)`. `sandbox/FGH.v` uses fuel; the cleanup for
   `Contender.v` should switch to `Fix` so no axioms are needed.
3. `term_depth (embed t) = term_depth t` and
   `eval_L6 (embed t) = eval_STLC t`, by routine structural induction
   replicating `interp_tApp`/`interp_tLam`/etc.
4. `maxBy`-style lemmas for L6 — these mirror those for STLC+NatRec
   line by line, with one extra constructor case each.
5. `forall n, n < FGH big_ord (S n)` — the only "hard" arithmetic fact;
   needs the basic FGH inequality `n < f_alpha(n+1)` for nonzero alpha,
   provable by induction on alpha along the fundamental sequence.

### A.4.1 Termination reality check

The current `sandbox/FGH.v` uses a fuel argument. Promoting it directly means
replacing that fuel with a real total definition. A quick standard-library
search did not turn up a ready-made ordinal notation/well-foundedness library
in the installed Rocq distribution, so the likely paths are:

1. Define an explicit CNF ordinal ordering and prove it well-founded.
   Then define `FGH_total` by `Fix` over the relation that contains
   `ord_pred a < a` and `ord_fund_seq a n < a`.
2. Avoid general runtime ordinal recursion in the first promoted contender:
   hard-code one large ordinal family with structural recursion over finite
   indices, e.g. a tower-specific diagonal hierarchy.
3. Keep `tFGH` as a primitive whose Coq denotation is specified by a
   separately proven total relation, then extract the executable function
   through a Bove-Capretta construction in the style of `System_F.v`.

The tempting measure `(ord_size a, n)` is not viable: fundamental sequences
can increase syntactic size, e.g. `omega^2[n] = omega * n`. So the descent has
to be ordinal-semantic, not tree-size-semantic.

### A.5 Why pick this

* Cleanly subsumes STLC+NatRec via embedding.
* Compact CNF ordinals — Grow is "just one term constructor".
* Computable; no axioms; small Coq footprint (`sandbox/FGH.v` is ~120
  lines and `sandbox/L6.v` adds ~100 more).
* Genuinely structurally stronger: STLC+NatRec at fixed depth `d`
  cannot uniformly express `f_alpha` for `alpha` close to its own
  proof-theoretic limit; L6 at the same depth can name those `alpha`
  cheaply because each `ocons`/`oz` costs constant depth.

### A.6 Risks / unknowns

* The fuel-vs-Fix question is the main engineering issue. Switching to
  well-founded recursion is mechanical but adds dependent pattern
  matching plus an `Acc` argument. The proof strategy in
  `eval_triple` from `System_F.v` is a useful reference.
* The Coq ord representation must remain reduction-friendly under
  `vm_compute`. The current shape (no proof obligations baked in) is
  fine.
* CNF is bounded by `epsilon_0`. To go higher you'd add a Veblen
  hierarchy or Bachmann–Howard notation; both blow up the ordinal data
  type and the fundamental-sequence definition. Probably overkill for
  a single contender bump.

---

## Approach B — System F (impredicative polymorphism)

Adding `Forall a. ...` types and type abstraction/application makes the
language System F. The functions `Nat -> Nat` definable in System F are
exactly those provably total in second-order Heyting arithmetic (HA²),
which is strictly stronger than what System T (= STLC+NatRec) can do.

The repo already has `System_F.v`, which contains:

* a normalization proof for closed System F terms via Girard's
  computability predicates,
* a Bove–Capretta–style well-founded evaluator (`eval_f`).

So the pieces are partly in place. Open work:

1. `term_depth` and `termsUpTo` for System F (must enumerate up to a
   depth, including type-abstraction structure).
2. A computable evaluator extracting a `nat` for closed terms of `Nat`
   type. `eval_f` is close but uses a value type; we'd want to read
   off Church numerals or a primitive `Nat`.
3. An embedding from STLC+NatRec into System F. This is standard:
   `Nat` becomes `forall X. X -> (X -> X) -> X` (Church), `0` becomes
   `Lam X. lam x:X. lam s:X->X. x`, etc. Fitting this into the
   `term_depth` budget requires care because Church numerals are
   slightly deeper than primitive numerals.
4. A separate `Grow`. System F itself does not give us a free
   primitive faster than what System T can already do — the strength
   gain is in *what's definable in finite depth*, not a specific
   built-in. We'd need to commit to either:
   * a non-trivial polymorphic witness (e.g. a Church-encoded
     transfinite iterator), or
   * a hybrid: System F + a small extra primitive.

Pros: principled, leverages existing infrastructure, gives a
qualitative jump in proof-theoretic strength.

Cons: heavy lift. The depth-bounded enumeration is fiddlier than for
STLC+NatRec because of two binders (term-level and type-level) and
two `tApp` analogues. The current `System_F.v` evaluator depends on
`FunctionalExtensionality`; the existing axioms list for the project
is empty, and that has to be preserved.

## Approach C — System T + bar recursion (Spector)

Bar recursion is the canonical "strictly above System T but still
constructive" extension. Adding the bar recursor at type `nat` gives a
system whose totality matches HA² (this is Spector's interpretation of
analysis). In practice:

```
BR : (forall (s : list nat) (n : nat -> nat),
        (... termination predicate ...) ->
        A) -> ...
```

The simplest variant is "Spector's bar recursion at type `nat`": a
recursor over finite sequences with an extension condition.

Pros: principled and proof-theoretically correct; exactly the right
"one step beyond System T".

Cons: the formal definition is significantly heavier than CNF
ordinals; termination requires a proof about extensions, not just an
ordinal descent. Probably more work than Approach A for less concrete
gain at the given depth budget.

## Approach D — A reflection primitive

Add a primitive

```
tEval : tpNat -> tpNat
```

evaluating to `largest_STLCNatRec_nat_of_depth n` on input `n`.

This sounds appealing because the new contender literally has access to
"the answer at smaller depths". The 2026-04-30 sandbox shows that the
mechanical path is extremely short:

* `sandbox/ReflectPrev.v` adds `tPrevMax : Nat -> Nat`.
* The term `S (tPrevMax 42)` has depth 45 using naive unary `42`.
* The extended depth search `largest_reflect_nat_of_depth 45` formally
  beats `contender_5`.

The previous dismissal of this route as "just primitive recursive" was too
quick. The syntax enumeration is primitive recursive, but the uniform
interpreter for arbitrary System T terms is exactly where the proof-theoretic
strength lives. The current contender already exploits that uniform
meta-level evaluator by taking a maximum over all depth-42 System T terms.
Making the previous evaluator available as a primitive in a new object
language is therefore a genuine staged-reflection move, not obviously a mere
depth optimization.

Pros:

* Shortest route to a verified next contender.
* The proof is basically the existing `maxBy` lower-bound proof plus one new
  constructor case.
* Can be made systematic: define `R_0(d) = largest_STLCNatRec_nat_of_depth d`
  and `R_{k+1}(d)` as the depth-`d` maximum of STLC+NatRec plus a primitive
  `R_k : Nat -> Nat`.

Cons:

* Aesthetic risk. It may read as "the previous contender, but reflected as an
  oracle", even though it is still constructive and finite.
* It is philosophically closer to a staged evaluator hierarchy than to a
  familiar mathematical growth hierarchy like FGH/Goodstein.
* The current sandbox uses unary `42`, so the witness budget is 45. This is
  fine for a next contender, but a promoted version should either accept the
  larger budget explicitly or add small arithmetic/reification helpers to make
  the argument term less silly.

Verdict: keep as a serious fallback, and possibly as its own line of attack:
`Reflect_k` is mechanically cleaner than FGH totality and can be pushed to
large finite `k` by structural recursion on `k`.

### Approach D.1 — stratified reflection tower

Generalize the sandbox from one previous maximum to a tower:

```coq
R 0 d     = largest_STLCNatRec_nat_of_depth d
R (S k) d = largest_{STLC+NatRec+tPrevMax_k}_nat_of_depth d
```

where `tPrevMax_k n` denotes `R k n`.

For every `k`, the language at level `S k` contains a term

```coq
S (tPrevMax_k c)
```

so

```coq
R k c < R (S k) (depth(c) + 2)
```

by the same proof as `sandbox/ReflectPrev.v`. With a monotonicity lemma for
`R k d` in `d`, one can chain this at a fixed comfortable depth. For example,
choose `D = 50`; then `R 42 D` should dwarf the one-step reflective candidate
while requiring only a structurally recursive Coq definition over the level
parameter.

This is probably the fastest way to generate a much larger formally verified
number if the contest accepts staged reflective languages. **Done as of the
2026-04-30 follow-up:** see `sandbox/ReflectTower.v`. The mechanical bound
`R_tower 100 342` is proved beyond `contender_5` in roughly 3.5 s of
compile time, with no axioms beyond `FunctionalExtensionality`.

### Approach D.2 — second-order reflection (the tower as a primitive)

`R_tower : nat -> nat -> nat` is now itself a Coq function of two `nat`
arguments. Approach D.1 used it externally — every level was a Coq
`Fixpoint` step. Approach D.2 internalises it as a primitive in yet another
reflective language `L_RT`:

```coq
tRTower : tpNat -> tpNat -> tpNat
```

interpreted as `R_tower`. Inside `L_RT`, the witness term

```coq
S (tRTower (natlit K) (natlit D))   (* eval = S (R_tower K D) *)
```

has term_depth `max(K + 3, D + 2) + 1 = max(K + 4, D + 3)`. Choosing the
internal depth budget `D'` for `L_RT` to be large enough to contain the
witness term, the simplest safe instantiation (with unary `natlit`) is to
reuse the already-proved pair `(K, D) = (100, 342)` from D.1. This gives a
witness depth of `345`, and the `L_RT` max at depth 345 is therefore at least
`S (R_tower 100 342)`, hence strictly beyond `contender_5`.

This is now fully materialized in `sandbox/ReflectRTower.v`, which proves
`Contender.contender_5 < largest_RT_nat_of_depth 345` via exactly that
witness.

Why this is interesting:

* The level argument is now *internal*: the depth-bounded enumeration in
  `L_RT` automatically picks the best `(K, D)` pair, so we no longer have
  to hard-code a level number in the contender definition.
* The same Opaque-protection trick from D.1 applies: `R_tower` should be
  marked `Opaque` (or its body kept hidden behind a thin abstraction) so
  the kernel does not try to fully evaluate `R_tower K D` while
  type-checking the contender bound.
* This iterates: Approach D.3 primitivizes `largest_RT_nat_of_depth` (now
  demonstrated in `sandbox/ReflectRTower3.v`),
  Approach D.k would have a length-`k` chain of meta-reflective layers.
  In each step, the previous "diagonal" is unwrapped and made addressable
  inside the new language.

Cons / open questions:

* The proof obligation is essentially the same as D.1 — a single-step
  witness lemma plus a `lowerbound_maxBy` invocation — so D.2 does not
  yield a *qualitatively* stronger growth rate. It simply makes the
  level-vs-depth tradeoff smoother.
* If the contest objects to D.1 on aesthetic grounds (a contender whose
  definition mentions a depth-bounded maximum function), it will object
  to D.k for the same reason — only more so.
* The natural endpoint of this chain is *not* an enumeration-of-an-
  enumeration tower at all but a transfinite ordinal-indexed FGH-style
  hierarchy, i.e. Approach A. From that perspective the staged reflection
  tower is a finite-rank approximation to Approach A's `f_alpha` with
  `alpha < epsilon_0` in disguise.

A concrete sandbox plan, parallel to ReflectTower.v:

1. Lift the parameterized reflective language to take *two* oracles,
   `prevMax : nat -> nat` and `prevMax2 : nat -> nat -> nat`.
2. Add `tRTower` with the obvious typing.
3. Reuse the same witness machinery, with witness
   `tApp tS (tApp (tApp tRTower (natlit K)) (natlit D))`.
4. Define `R_tower2 : nat -> nat -> nat -> nat` recursive on the *outer*
   level, with `R_tower2 0 = R_tower` and `R_tower2 (S k')` adding one
   layer of `tRTower` reflection.
5. Prove a `R_tower2_step` lemma and a chain. Mark `R_tower` opaque
   beforehand so depth-(D large) terms do not blow up the kernel.

Estimated incremental cost: roughly the same as ReflectTower.v itself (one
sandbox afternoon), since all the syntax/maxBy/witness pieces transfer.

## Approach E — Higher-order primitive recursion at one specific
type

A weaker, more surgical version of Approach A: pick one specific big
ordinal `alpha < epsilon_0`, hard-code `f_alpha : nat -> nat` as a
single primitive `tBigGrow : tpNat -> tpNat`, and stop. This is
essentially the "`Grow x = ack 5 42 (S x)`" suggestion from the
earlier IDEAS.md, but with a much bigger seed.

Pros: minimal Coq footprint; the FGH definition lives only at proof
time, not in the term grammar; depth budget for using it is just
`tApp tBigGrow (embed t*)` ≈ 1 + 42 = 43. Easy `term_depth`
arithmetic.

Cons: the choice of `alpha` is a magic constant in the language
definition. Not as principled as making the ordinal itself a runtime
input via `tpOrd`. Also less reusable — once we want to push further
later we have to carve another notch in the language rather than
varying the ordinal.

Verdict: useful as a fallback if Approach A's runtime ord
representation proves too painful to formalize cleanly.

## Approach F — A hydra / Goodstein primitive

Add `tHydra : tpNat -> tpNat` where `tHydra n` is the number of steps
until the Kirby–Paris hydra of size `n` dies, or equivalently the
number of steps in the Goodstein sequence starting at `n`. These
functions grow at exactly `f_{epsilon_0}` rate, which is the natural
target.

Pros: very principled — Goodstein and Kirby–Paris are *the* canonical
`epsilon_0`-strength examples; a single primitive carries genuine
weight.

Cons: defining the hydra game (or hereditary base-`n` representations
for Goodstein) and proving it terminates totally inside Coq is a
substantial project on its own. There's a known Coq formalization of
Goodstein by Castéran et al. (`Cantor` / `hydras`) which could be
adapted but adds a large dependency.

## Recommendation / next concrete step

State of play after the 2026-04-30 follow-up:

* **Approach D.1 is mechanically done in sandbox, axiom-free.**
  `sandbox/ReflectTowerNoAx.v` proves
  `Contender.contender_5 < R_tower 100 342` with no axioms (`Print
  Assumptions` reports a closed global context).  The earlier
  `sandbox/ReflectTower.v` is the same theorem with the axiom dependency
  inherited from `FunctionalExtensionality`; both compile in ~3 s.  The
  no-axioms cleanup goes through by restricting `interp_tApp` to
  `tpNat`-typed arguments (where `cast tpNat a = a` is definitional) and
  dropping `interp_tLam` / `cast_impl_same` (which are unused for the
  witness chain).
* **Approach D.2 now has unary-literal, small-witness, and computed-K/D
  axiom-free versions.**  `sandbox/ReflectRTower.v` proves
  `Contender.contender_5 < largest_RT_nat_of_depth 345` (witness =
  `S (tRTower 100 342)`, depth 345).  `sandbox/ReflectRTowerSmall.v`
  proves `Contender.contender_5 < largest_RT_nat_of_depth 48` (witness
  = `S (tRTower 1 45)`, depth 48) with no axioms, by importing the
  axiom-free `ReflectTowerNoAx` and using only the smallest case of the
  step lemma.  `sandbox/ReflectRTowerComputed.v` proves the same kind
  of bound with a computed witness `S (tRTower (pow2 1) (pow2 6))`,
  where `pow2 1 = 2` and `pow2 6 = 64`, at depth 20 and with a closed
  global context.  It also records the D-only intermediate witness
  `S (tRTower 1 (pow2 6))` at depth 19.  These files record the same
  kernel conversion trap:
  `eval`/`maxBy`/the enumerator must be made `Opaque` *before* applying
  the maxBy lower-bound lemma at a concrete depth, or Coq will try to
  run the depth-bounded search during conversion.
* **Approach D.3 (meta-reflection over the D.2 max) is now demonstrated at depth 23.**
  `sandbox/ReflectRTower3.v` defines `prevMax2 d := largest_RT_nat_of_depth RTower d`
  and applies the one-step `ReflectTowerNoAx` witness trick to get a strict
  inequality `contender_reflect_rtower_computed < contender_reflect_rtower3`,
  hence also `Contender.contender_5 < contender_reflect_rtower3`, with a closed
  global context.  The same `Opaque` barrier is needed here too to keep the kernel
  from running the D.2 search during the definitional `change` step.
* **Approach A's well-foundedness obstacle is now bypassed via Brouwer
  ordinal notations.** `sandbox/Brouwer.v` defines a Brouwer-ordinal
  inductive type whose `Blim : (nat -> Brouwer) -> Brouwer` constructor
  bakes the fundamental sequence into the data; pure structural Fixpoint
  on Brouwer ordinals goes through the W-type guard, so `FGH`, `Hardy`,
  `Badd`, `Bmul`, `omega_pow`, and `epsilon_0` all live as plain
  `Fixpoint`s with no axioms, no `Acc`, no fuel.  `BigGrow := FGH
  epsilon_0 : nat -> nat` is therefore a totally defined Coq function.
  The remaining work for Approach A / E is now a *connector* lemma --
  bounding STLC+NatRec evals at depth 42 by `f_alpha(42)` for some
  `alpha < epsilon_0` -- not a foundational well-foundedness proof.

Three credible next concrete steps, ordered by ambition:

### Track 1 — promote ReflectTower to Contender.v (low risk)

The "no-axioms cleanup" sub-step is now done as
`sandbox/ReflectTowerNoAx.v`; the axiom dependency was via `cast_same`
in the dependent typed evaluator and is removed by restricting
reduction lemmas to `tpNat`-typed arguments (`cast tpNat = id` is
definitional, no extensionality required).

What remains for actual promotion to `Contender.v`:

1. Pick a defensible level/depth pair (`R_tower 100 342` works; `R_tower
   k (3k+42)` for any `k` works; `R_tower 1 45` is the smallest-witness
   variant in `ReflectRTowerSmall.v`).
2. Verify the 15 s / 60 s budgets.  Both
   `sandbox/ReflectTowerNoAx.v` and `sandbox/ReflectRTowerSmall.v`
   already comfortably fit; the contender-shape rebuild on top of
   `Contender.v`'s existing infrastructure should too.
3. Decide whether the contest format accepts a contender that names a
   reflection oracle. If yes, this is the next contender. If no, this
   sandbox line stays honorable but unofficial.

### Track 2 — finish Approach A (medium risk, principled)

The previous well-foundedness blocker is now bypassed by
`sandbox/Brouwer.v`'s Brouwer-ordinal definition of `FGH` and `Hardy`.
The remaining concrete sub-tracks are:

* **Brouwer-based contender language (Approach E in disguise).**  Add
  `tBigGrow : tpNat -> tpNat` as a primitive interpreted as
  `Brouwer.BigGrow := Brouwer.FGH Brouwer.epsilon_0`.  Lift the
  syntax/maxBy/enumeration scaffolding from `sandbox/ReflectTowerNoAx.v`,
  drop `tPrevMax` and add `tBigGrow`, prove a `tBigGrow`-using witness
  beats `contender_5`.  The mechanical shape is the same maxBy
  lower-bound argument as the reflection-tower sandboxes; the
  *interesting* obligation is the strict-inequality step, which needs a
  meta-theorem bounding STLC+NatRec eval at depth 42 by `f_alpha(42)`
  for some `alpha < epsilon_0`.  That meta-theorem (the proof-theoretic
  ordinal of System T) is true, well-known, and a real piece of
  formalization work; it is the only remaining gate.
* **Brouwer ordinals + ordinal *runtime input* (full Approach A).**
  Expose Brouwer ordinals as a *type* in the contender language --
  add `tpOrd`, `tBz`, `tBsucc`, `tBlim`, `tFGH : tpOrd -> tpNat ->
  tpNat`.  Strictly more general than the previous bullet, but
  formally more delicate because Brouwer ordinals contain functions
  (`Blim : (nat -> Brouwer) -> Brouwer`), which interacts with the
  syntax-of-types convention.
* **Direct CNF well-founded recursion.**  Still possible; the
  `sandbox/FGH.v` skeleton plus a `well_founded ord_lt` proof would
  give the same expressive power as Brouwer-based FGH but with a
  flatter representation.  Worth doing only if Brouwer's
  closure-in-ordinal interaction with the contender language proves
  unwieldy.

Pick whichever seems most tractable for the contributor. The existing
`sandbox/Brouwer.v`, `sandbox/L6.v`, and `sandbox/FGH.v` are aligned
with the first, second, and third of these respectively.

### Track 3 — push reflection further (post-D.2, low risk, marginal gain)

Approach D.2 is now mechanically demonstrated in `sandbox/ReflectRTower.v`
(unary literals, depth 345), `sandbox/ReflectRTowerSmall.v` (smallest
witness, depth 48, no axioms), and `sandbox/ReflectRTowerComputed.v`
(computed `pow2 1` / `pow2 6` K/D arguments, depth 20, no axioms).
If Track 1 ships and staged reflection is accepted, the next incremental
pushes are:

* **Computed-K/D generalization**: turn the one-off `pow2_at 0 (natlit n)`
  artifact into a small library of level-indexed object-language
  arithmetic combinators.  The immediate upgrades are trying
  `pow2 (pow2 3)` or tetration-shaped arguments, and proving generic
  evaluation lemmas instead of one-off `vm_compute` facts.  The caution
  is now concrete: every reusable lambda template must be parameterized
  by its ambient de Bruijn level count.
* **D.3**: primitivize `largest_RT_nat_of_depth` itself as the next
  reflective oracle and iterate again.

### Approach B as a long-term differentiator

Approach B (System F) is the natural target after either Track 1 or
Track 2 has been promoted. It provides a different axis of strength
(impredicative polymorphism rather than higher ordinal indexing) and the
existing `System_F.v` already has a normalization proof. It is heavier
than Approaches A/D.1 because the depth-bounded enumeration over
type-and-term-binders is fiddlier, but it is also genuinely
qualitatively new — once it lands, future contenders can be built by
adding type-level structures (System Fω, Calculus of Constructions,
inductive families) rather than chasing finer ordinal notations.

## Executive assessment

The fork has made real progress. It has several mechanically verified sandbox candidates that beat `contender_5`, many of them axiom-free. But the current documented judgment is correct: the reflection/oracle family is probably too close to the “don’t be lazy” line for an upstream PR.

The most important correction I’d make to the plan is this:

**The Brouwer/BigGrow connector lemma is necessary only for a closed-form contender like `Definition contender_6 := BigGrow N`. It is not necessary for a clean language-extension contender.**

There is a simpler and cleaner route:

> Define a new depth-bounded language equal to STLC+NatRec plus a fresh primitive
> `tBigGrow : Nat -> Nat`, interpreted as `Brouwer.BigGrow`.
> Then prove that its depth-44 maximum contains the term
> `tBigGrow (S (embed old_best))`, where `old_best := Contender.largest_of_depth 42`.

This candidate’s **definition** need not mention `contender_5`, `largest_STLCNatRec_nat_of_depth`, `R_tower`, or any previous-max oracle. The proof naturally uses the previous maximum as a witness, which is exactly what these max-over-language proofs are supposed to do.

That looks like the next best experiment.

---

## What has been tried

### 1. Baseline / current contender analysis

The current contender is:

```coq
Definition contender_5 : nat := largest_STLCNatRec_nat_of_depth 42.
```

The docs correctly identify it as a depth-bounded maximum over raw STLC+NatRec syntax. The baseline sandbox records small-depth growth and the old witnesses:

```text
length (termsUpTo 1) = 2
length (termsUpTo 2) = 10
length (termsUpTo 3) = 146
length (termsUpTo 4) = 24976

largest_STLCNatRec_nat_of_depth 1 = 0
... depth 4 = 3

term_depth ack_reified = 26
term_depth contender_4''_reified = 30
```

The important takeaway is right: depth 42 has slack beyond the old Ackermann witness, but it is still “System T at bounded syntactic depth.”

### 2. CNF ordinal / L6 prototype

`sandbox/FGH.v` and `sandbox/L6.v` prototype:

```coq
tpOrd
tOZ
tOCons
tFGH : tpOrd -> tpNat -> tpNat
```

This was useful as a proof of concept, but the CNF version uses fuel. The docs already recognize that promotion would require either a real well-founded recursion proof or a different encoding.

My view: keep these files as historical scaffolding. The Brouwer-ordinal version supersedes them for the “total FGH in Coq” part.

### 3. Reflection family

The reflection line is impressive mechanically:

| File                      | Idea                                     | Status                                                 |
| ------------------------- | ---------------------------------------- | ------------------------------------------------------ |
| `ReflectPrev.v`           | STLC+NatRec plus `tPrevMax : Nat -> Nat` | Beats `contender_5` at depth 45                        |
| `ReflectTower.v`          | finite tower `R_tower k d`               | Beats via `R_tower 100 342`; originally FunExt-tainted |
| `ReflectTowerNoAx.v`      | axiom-free tower                         | Same theorem, closed global context                    |
| `ReflectRTower.v`         | primitive `tRTower : Nat -> Nat -> Nat`  | Beats via `S (tRTower 100 342)`                        |
| `ReflectRTowerSmall.v`    | smallest `(K,D)=(1,45)`                  | Beats at depth 48, axiom-free                          |
| `ReflectRTowerComputed.v` | computes K/D internally using NatRec     | Beats at depth 20                                      |
| `ReflectRTower3.v`        | reflects the D.2 max itself              | Beats the computed D.2 candidate                       |

The engineering around `Opaque` barriers is good and important. The repo correctly learned that Coq’s conversion checker must not be allowed to unfold a depth-bounded search at concrete depths like 42, 48, 345, etc.

My judgment: this track is **technically successful** and **submission-risky**. It uses previous maxima/oracles as part of the candidate definition, so the user’s “too close to violating don’t-be-lazy” call is right.

Also, I would stop calling this axis “impredicative reflection.” It is staged reflection/oracle reflection. “Impredicative” should be reserved for the System F track.

### 4. Brouwer ordinal FGH

`sandbox/Brouwer.v` is the cleanest fresh engine so far:

```coq
Inductive Brouwer : Type :=
| Bz    : Brouwer
| Bsucc : Brouwer -> Brouwer
| Blim  : (nat -> Brouwer) -> Brouwer.

Definition epsilon_0 : Brouwer := Blim omega_tower.

Fixpoint FGH (a : Brouwer) (n : nat) : nat := ...
Definition BigGrow (n : nat) : nat := FGH epsilon_0 n.
```

This is a very nice move. It avoids the CNF well-foundedness problem because the fundamental sequence is stored in the `Blim` constructor, making the FGH definition structurally recursive.

The useful proved facts are:

```coq
Lemma FGH_ge : forall a n, n <= FGH a n.
Lemma BigGrow_ge : forall n, n <= BigGrow n.
Lemma BigGrow_gt_S : forall n, n < BigGrow (S n).
```

That last lemma is enough to build a very strong next contender when `BigGrow` is used as a primitive applied to the embedded previous winner.

### 5. BigGrow + oracle hybrids

`BigGrowPrevMax.v` and `BigGrowRTower.v` combine Brouwer-FGH with the reflection/oracle machinery. They are mechanically strong but remain in the same aesthetic danger zone.

`BigGrowPrevMax.v` proves the generic pattern:

```coq
prevMax d <
largest_BGPrev_nat_of_depth prevMax (d + 4)
```

via the witness:

```coq
tBigGrow (S (tPrevMax d))
```

This proof pattern is valuable. But for submission, I would replace `tPrevMax d` with `embed old_best`.

That gives the same diagonal punch without making the previous max an oracle in the candidate language.

---

## What is planned

The documented game plan in `AGENTS.md` is:

1. Do not submit oracle-based sandboxes.
2. Prefer fresh engines whose definitions do not reference `largest_STLCNatRec_nat_of_depth`, `R_tower`, `termsUpTo`, etc.
3. Prioritize the Brouwer-FGH connector lemma.
4. Explore higher Brouwer ordinals, Veblen functions, System F, Goodstein/hydra, TREE/SCG/WORM, bar recursion, and alternative evaluation models.

That is mostly sensible, but I would revise the priority order.

The connector lemma is needed for this kind of candidate:

```coq
Definition contender_6 : nat := BigGrow 50.
```

It is **not** needed for this kind:

```coq
Definition contender_6 : nat :=
  largest_STLCNatRec_plus_BigGrow_nat_of_depth 44.
```

The second form is still clean: its definition is a max over a fresh object language, not a wrapper around `contender_5`.

---

## Main recommendation: build the BigGrow-embedding contender

This is the idea I would try next.

Define a new object language:

```coq
Inductive term_BG :=
| tVar     : nat -> term_BG
| tLam     : type -> type -> term_BG -> term_BG
| tApp     : term_BG -> term_BG -> term_BG
| tO       : term_BG
| tS       : term_BG
| tNatRec  : type -> term_BG
| tBigGrow : term_BG.   (* Nat -> Nat *)
```

Its evaluator is the old STLC+NatRec evaluator plus:

```coq
tBigGrow : tpArr tpNat tpNat
```

interpreted as:

```coq
sandbox.Brouwer.BigGrow
```

Then define:

```coq
Definition contender_6 : nat :=
  largest_BG_nat_of_depth 44.
```

The proof witness is not part of the definition:

```coq
Definition old_best : Contender.term :=
  Contender.largest_of_depth 42.

Definition witness_6 : term_BG :=
  tApp tBigGrow (tApp tS (embed old_best)).
```

The intended proof facts are:

```coq
Lemma old_best_depth :
  Contender.term_depth old_best <= 42.

Lemma embed_depth :
  forall t, term_depth_BG (embed t) = Contender.term_depth t.

Lemma witness_6_depth :
  term_depth_BG witness_6 <= 44.

Lemma embed_eval_nat :
  forall t,
    eval_BG (embed t) = Contender.eval t.

Lemma eval_witness_6 :
  eval_BG witness_6 =
    sandbox.Brouwer.BigGrow (S Contender.contender_5).

Lemma contender_6_margin :
  sandbox.Brouwer.BigGrow (S Contender.contender_5) <= contender_6.

Theorem contender_5_lt_contender_6 :
  Contender.contender_5 < contender_6.
```

The last theorem follows immediately from:

```coq
Brouwer.BigGrow_gt_S : forall n, n < BigGrow (S n)
```

This would prove not just a strict win, but a strong lower bound:

```coq
BigGrow (S contender_5) <= contender_6
```

That is a much better “decisively beats by a big margin” statement than merely proving `contender_5 < contender_6`.

### Proof engineering details

The only delicate part is `embed_eval_nat`.

Do **not** prove embedding preservation by equality of higher-type denotations unless you are comfortable importing functional extensionality. Use a logical relation instead:

```coq
RelVal tpNat x y := x = y

RelVal (tpArr A B) f g :=
  forall x y, RelVal A x y -> RelVal B (f x) (g y)
```

Then prove an environment-parametric lemma:

```coq
Lemma embed_interp_related :
  forall e_old e_new t,
    RelEnv e_old e_new ->
    RelPack
      (Contender.interp_term e_old t)
      (interp_BG e_new (embed t)).
```

At `tpNat`, this collapses to equality of natural-number evaluations. This avoids function extensionality and also handles lambdas naturally.

Because `Contender.v` uses a total untyped evaluator with `cast` and `error`, also prove a cast lemma:

```coq
Lemma cast_related :
  forall A B x y,
    RelVal A x y ->
    RelVal B (cast B x) (cast B y).
```

That is the key lemma that makes ill-typed raw terms harmless. The previous maximum is over raw syntax, not only well-typed syntax, so this matters.

### Why this is cleaner than the connector route

The connector route tries to prove:

```coq
Contender.contender_5 < BigGrow N
```

for a fixed small `N`.

That requires bounding every depth-42 STLC+NatRec evaluation by some explicit FGH level below `epsilon_0`. True, but substantial.

The embedding route proves:

```coq
Contender.contender_5
  < BigGrow (S Contender.contender_5)
  <= largest_BG_nat_of_depth 44
```

without bounding System T at all. It uses the old maximizing term as a syntactic witness inside the larger language. That is the standard max-language diagonalization pattern and does not make the candidate definition depend on the old contender.

---

## Comments on the connector lemma plan

The proposed connector lemma is still useful if you want a very elegant closed-form contender:

```coq
Definition contender_6 := BigGrow 43.
```

But I would downgrade it from “next required step” to “nice later step.”

Also, the sketch in `IDEAS.md` looks too optimistic in one place. It suggests a possible bound like:

```coq
eval t <= FGH omega 42
```

for depth-42 STLC+NatRec terms. I would not trust that. Depth 42 permits higher-type uses of `NatRec`, and finite type levels of Gödel T climb through towers of `omega`, not merely `omega`.

A safer connector target would be something like:

```coq
eval t <= FGH (omega_tower (d + c)) (d + c)
```

for `term_depth t <= d`, with `c` deliberately loose. Then use:

```coq
FGH (omega_tower N) N = FGH (epsilon_0[N]) N <= FGH epsilon_0 N
```

morally, though formalizing the ordinal monotonicity is another task.

For a first connector, I would avoid trying to be sharp. Make the ordinal assignment hilariously overpowered and easy to maintain.

---

## Important issue: `BrouwerHigh.v` ordinal labels look wrong

`sandbox/BrouwerHigh.v` is a good stress test of the Brouwer encoding, but I would not rely on its mathematical names yet.

This part is suspect:

```coq
Definition epsilon_omega : Brouwer := Blim epsilon_at.
Definition zeta_0 : Brouwer := epsilon_omega.
```

The comments say `zeta_0` is the smallest fixed point of `next_epsilon`, and that this equals `epsilon_omega`. That is not the standard ordinal story. `epsilon_omega` is the limit of finite epsilon numbers:

```text
epsilon_0, epsilon_1, epsilon_2, ...
```

But `zeta_0` is the first fixed point of the function `alpha ↦ epsilon_alpha`, usually reached by a sequence more like:

```text
0,
epsilon_0,
epsilon_{epsilon_0},
epsilon_{epsilon_{epsilon_0}},
...
```

So `epsilon_omega` is far below `zeta_0`.

Similarly, the current:

```coq
Definition Gamma_0 := Blim phi_2_iter.
```

does not look like a faithful Feferman–Schütte `Gamma_0` definition unless the preceding `phi_2` machinery is fixed and generalized.

My advice:

1. Rename current definitions conservatively until fixed:

   ```coq
   epsilon_omega
   pseudo_zeta_0
   pseudo_Gamma_0
   ```

   or keep them as “Brouwer stress-test ordinals.”

2. Add a genuine epsilon-indexing function:

   ```coq
   Fixpoint epsilon_indexed (a : Brouwer) : Brouwer :=
     match a with
     | Bz       => epsilon_0
     | Bsucc a' => next_epsilon (epsilon_indexed a')
     | Blim f   => Blim (fun n => epsilon_indexed (f n))
     end.
   ```

3. Then define:

   ```coq
   Fixpoint iter_eps (n : nat) (a : Brouwer) : Brouwer :=
     match n with
     | 0 => a
     | S n' => epsilon_indexed (iter_eps n' a)
     end.

   Definition zeta_0 : Brouwer :=
     Blim (fun n => iter_eps n Bz).
   ```

4. Do not claim `Gamma_0` until there is either a genuine Veblen function

   ```coq
   phi : Brouwer -> Brouwer -> Brouwer
   ```

   or a carefully justified specialized construction.

The total Coq functions in `BrouwerHigh.v` may still be perfectly usable as large total functions. The issue is the mathematical labeling.

---

## Advice on the reflection track

Keep the reflection files. They are useful. But I would not put them on the upstream path unless the maintainer explicitly blesses staged reflection.

What they are good for:

* reusable `maxBy` lemmas,
* opacity discipline,
* de Bruijn-level arithmetic templates,
* proof patterns for lower-bounding a depth-bounded max by an internal witness,
* demonstrating axiom-free cleanup techniques.

What they are bad for:

* convincing a skeptical maintainer that the new contender is not just “the old contender as an oracle.”

The current `AGENTS.md` conclusion is right: stop adding “one more oracle layer” unless it teaches something new.

---

## Advice on System F

The System F track is interesting but not near-term. `System_F.v` gives normalization infrastructure, but a contender needs more:

* depth-bounded enumeration over type and term binders,
* a natural-number representation,
* extraction of a numeric evaluator,
* an embedding of STLC+NatRec,
* a concrete growth witness.

Also, System F is the place where “impredicative” language is accurate. I would keep it as a later differentiator after a Brouwer/BigGrow-based contender lands.

---

## Engineering recommendations

### Add a small build harness

Right now there is no `_CoqProject` or `Makefile` in the snapshot. Add one. Even a tiny harness helps future agents avoid folklore commands.

Example shape:

```makefile
COQC=coqc
COQCHK=coqchk

Contender.vo: Contender.v
	$(COQC) Contender.v

check-contender: Contender.vo
	$(COQCHK) Contender

check-brouwer:
	$(COQC) -Q . "" sandbox/Brouwer.v
	$(COQCHK) -Q . "" sandbox.Brouwer
```

For the serious candidate, add a target that checks only:

```text
Contender.v
sandbox/Brouwer.v
sandbox/BigGrowEmbed.v
```

Do not make the whole sandbox suite mandatory; some files are historical and intentionally exploratory.

### Test Coq 8.10.2 before upstream

`README.md` still says Coq 8.10.2. `AGENTS.md` says the local toolchain is Rocq 9.0.1. That is fine for exploration, but promotion needs a compatibility pass.

In particular:

* avoid `From Stdlib ...` in anything promoted,
* watch for changed module paths,
* avoid relying on Rocq 9-only behavior,
* keep `Nat.iter` compatibility in mind.

### Separate “definition purity” from “proof references”

The current game plan says to avoid definitions tied to:

```text
largest_STLCNatRec_nat_of_depth
interp_term
termsUpTo
largest_of_depth
```

That is a good rule for the **candidate definition**. But the proof necessarily references previous machinery. I would make the rule sharper:

> The new contender’s definition must not mention the previous contender’s maximum/search machinery.
> The proof may use the previous maximum to choose a witness and prove the strict inequality.

That distinction unlocks the BigGrow-embedding route.

---

## New ideas worth trying

### Idea 1: generic “Grow primitive” theorem

Do not bake `BigGrow` into the proof architecture too early. Prove a generic theorem:

```coq
Module Type GrowSig.
  Parameter grow : nat -> nat.
  Axiom grow_gt_S : forall n, n < grow (S n).
End GrowSig.
```

Then build the extended language once:

```coq
STLC+NatRec+tGrow
```

and prove generically:

```coq
largest_T_plus_grow_nat_of_depth 44 > contender_5.
```

Instantiate with:

```coq
grow := Brouwer.BigGrow
```

Later, instantiate with:

```coq
grow := fun n => FGH fixed_huge_ordinal n
grow := Goodstein
grow := Hardy epsilon_0
grow := fun n => BigGrow (S (BigGrow (S n)))
```

This turns the contender proof into a reusable theorem. The only per-engine obligations are totality and `grow_gt_S`.

### Idea 2: iterate `tBigGrow` inside the witness

Depth 44 gives:

```coq
BigGrow (S contender_5)
```

Depth 46 gives:

```coq
BigGrow (S (BigGrow (S contender_5)))
```

In general, depth `42 + 2k` gives `k` runtime iterations of `BigGrow` over the embedded previous max.

A tasteful submission might avoid arbitrary overkill and use depth 44. But as an experiment, a generic iterated-witness lemma would be nice:

```coq
Definition grow_witness_iter k old :=
  Nat.iter k (fun t => tApp tBigGrow (tApp tS t)) (embed old).

Lemma grow_witness_iter_depth :
  term_depth (grow_witness_iter k old_best) <= 42 + 2*k.
```

Then the repo can choose a depth after considering aesthetics.

### Idea 3: fix BrouwerHigh, then use a stronger primitive without hierarchy proofs

Once `BrouwerHigh.v` has correctly named higher ordinals, define:

```coq
Definition HugeGrow n := FGH Gamma_0 n.
```

To prove a language-extension contender beats `contender_5`, you do **not** need to prove `epsilon_0 < Gamma_0`. You only need:

```coq
forall n, n < HugeGrow (S n)
```

which follows from `FGH_ge`.

So higher ordinals can improve the actual value of the candidate without requiring formal ordinal-comparison machinery.

### Idea 4: closed-form contender as a later milestone

After the language-extension candidate, return to the connector lemma:

```coq
Definition contender_7 := BigGrow 50.
```

or

```coq
Definition contender_7 := FGH Gamma_0 50.
```

This would be aesthetically beautiful, but it is a separate proof project. I would not block the next contender on it.

---

## Suggested next concrete task

Create:

```text
sandbox/BigGrowEmbed.v
```

Start from `sandbox/BigGrowPrevMax.v`, but remove `tPrevMax`.

Keep:

* the `tBigGrow` primitive,
* the `termsUpTo`/`maxBy` machinery,
* the `lowerbound_maxBy` proof pattern,
* the opacity discipline.

Add:

* `embed : Contender.term -> term_BG`,
* `embed_depth`,
* `old_best_depth`,
* a logical-relation preservation proof,
* the witness `tBigGrow (S (embed old_best))`,
* the margin theorem:

  ```coq
  Brouwer.BigGrow (S Contender.contender_5) <= contender_bigGrowEmbed
  ```
* the final theorem:

  ```coq
  Contender.contender_5 < contender_bigGrowEmbed
  ```

If that compiles axiom-free and within budget, it is a much cleaner candidate than the current oracle-based sandboxes and probably the strongest immediate path forward.

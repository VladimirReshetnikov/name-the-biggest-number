(* Sandbox: combine BigGrow (Approach A / E, via Brouwer ordinals) with
   the reflection tower R_tower (Approach D.1).

   Two existing pieces:

   * sandbox/Brouwer.v defines [BigGrow := FGH epsilon_0 : nat -> nat]
     with the lemma [BigGrow_gt_S : forall n, n < BigGrow (S n)].
   * sandbox/ReflectTowerNoAx.v defines the reflection tower
     [R_tower : nat -> nat -> nat] and proves
     [R_tower 0 d < R_tower (S k) (S (S (S d)))] for any [k, d].
   * sandbox/BigGrowPrevMax.v defines a depth-bounded reflective max
     [largest_BGPrev_nat_of_depth] parameterized by a [prevMax] oracle,
     and the step lemma
     [prevMax d < largest_BGPrev_nat_of_depth prevMax (d + 4)].

   This file plugs [R_tower 1] (or any [R_tower (S k)]) in as the
   [prevMax] oracle, getting a contender that strictly beats
   [contender_5] using *both* axes of strength simultaneously.  No
   proof-theoretic-ordinal-of-System-T meta-theorem is required.

   Two flavors:

   1. Pure composition.  [BigGrow (S (R_tower 1 45))] is itself a Coq
      [nat] strictly larger than [contender_5].  No depth-bounded
      enumeration; just function composition.

   2. Layered through [largest_BGPrev_nat_of_depth].  The depth-bounded
      max for L_BG_Prev with prevMax := R_tower 1 at budget 49 is
      strictly larger than [R_tower 1 45], hence than [contender_5].

   Both have closed global contexts.  Compile from repo root, after
   sandbox/Brouwer.vo, sandbox/ReflectTowerNoAx.vo, and
   sandbox/BigGrowPrevMax.vo are built:

     coqc -Q . "" sandbox\BigGrowRTower.v
*)

Require Import Arith Lia.

Require Contender.
Require Import sandbox.Brouwer.
Require Import sandbox.ReflectTowerNoAx.
Require Import sandbox.BigGrowPrevMax.

Opaque Contender.largest_STLCNatRec_nat_of_depth.

(* The R_tower partial application we will reflect on. *)
Definition RT1 : nat -> nat :=
  sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower 1.

(* Lift the existing chain Contender.contender_5 < R_tower 1 45 into a
   one-line lemma we can compose with the [BigGrowPrevMax] machinery. *)

Lemma contender_5_lt_RT1_45 :
  Contender.contender_5 < RT1 45.
Proof.
  unfold Contender.contender_5, RT1.
  change (Contender.largest_STLCNatRec_nat_of_depth 42)
    with (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower 0 42).
  change 45 with (S (S (S 42))).
  apply (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower_step 0 42).
Qed.

(* -------------------------------------------------------------------- *)
(* Flavor 1: pure composition.                                           *)
(*                                                                       *)
(*   BigGrow (S (R_tower 1 45))                                          *)
(*                                                                       *)
(* By [BigGrow_ge], BigGrow (S x) >= S x > x.  Plug in x := R_tower 1 45 *)
(* and use the existing R_tower step bound.  No language extension       *)
(* needed; this is just a Coq nat. *)
(* -------------------------------------------------------------------- *)

Definition contender_BG_RT_simple : nat :=
  sandbox.Brouwer.BigGrow (S (RT1 45)).

Theorem contender_5_lt_BG_RT_simple :
  Contender.contender_5 < contender_BG_RT_simple.
Proof.
  unfold contender_BG_RT_simple.
  eapply Nat.lt_le_trans with (m := S (RT1 45)).
  - apply Nat.lt_lt_succ_r.
    exact contender_5_lt_RT1_45.
  - apply sandbox.Brouwer.BigGrow_ge.
Qed.

(* -------------------------------------------------------------------- *)
(* Flavor 2: depth-bounded enumeration over L_BG_Prev with prevMax = RT1.*)
(*                                                                       *)
(* The existing [BigGrowPrevMax.prevMax_lt_BGPrev] is parameterized by   *)
(* the oracle, so we can swap in RT1 for free.  Witness depth: 49 (= 45  *)
(* + 4 from the [tBigGrow (tApp tS (tApp tPrevMax (natlit 45)))] shape). *)
(* -------------------------------------------------------------------- *)

Definition contender_BG_RT_layered : nat :=
  sandbox.BigGrowPrevMax.BigGrowPrevMax.largest_BGPrev_nat_of_depth
    RT1
    (S (S (S (S 45)))).

Theorem contender_5_lt_BG_RT_layered :
  Contender.contender_5 < contender_BG_RT_layered.
Proof.
  eapply Nat.lt_trans with (m := RT1 45).
  - exact contender_5_lt_RT1_45.
  - unfold contender_BG_RT_layered.
    apply (sandbox.BigGrowPrevMax.BigGrowPrevMax.prevMax_lt_BGPrev RT1 45).
Qed.

(* -------------------------------------------------------------------- *)
(* Bonus flavor 3: stack the two on top of each other.  We have already  *)
(* proven that L_BG_Prev with prevMax = RT1 strictly beats [RT1 45]; now *)
(* we apply BigGrow once more on top, with [BigGrow_ge] to keep the      *)
(* lower bound chain monotone.                                           *)
(* -------------------------------------------------------------------- *)

Definition contender_BG_RT_stacked : nat :=
  sandbox.Brouwer.BigGrow (S contender_BG_RT_layered).

Theorem contender_5_lt_BG_RT_stacked :
  Contender.contender_5 < contender_BG_RT_stacked.
Proof.
  unfold contender_BG_RT_stacked.
  eapply Nat.lt_le_trans with (m := S contender_BG_RT_layered).
  - apply Nat.lt_lt_succ_r.
    exact contender_5_lt_BG_RT_layered.
  - apply sandbox.Brouwer.BigGrow_ge.
Qed.

(* All three flavors close under the global context. *)

Print Assumptions contender_5_lt_BG_RT_simple.
Print Assumptions contender_5_lt_BG_RT_layered.
Print Assumptions contender_5_lt_BG_RT_stacked.

(* Sandbox: computed-argument variant of D.2.

   This file builds on sandbox/ReflectRTowerSmall.v.  The previous
   small-witness artifact used the unary literal

       S (tRTower 1 45)

   at term_depth 48.  Here the D argument is computed in the object
   language by NatRec:

       S (tRTower 1 (pow2 6))

   where pow2 6 evaluates to 64.  Then it also computes the K argument:

       S (tRTower (pow2 1) (pow2 6))

   which evaluates to S (RTower 2 64) at depth 20.  The proof uses one
   more R_tower_step and ReflectTowerNoAx.R_tower_S_d_mono to pad the
   R_tower 2 48 lower bound up to R_tower 2 64.

   Compile from the repository root, after Contender.vo,
   sandbox/ReflectTowerNoAx.vo, and sandbox/ReflectRTowerSmall.vo exist:

     coqc -Q . "" sandbox\ReflectRTowerComputed.v
*)

Require Import Arith Lia.

Require Contender.
Require Import sandbox.ReflectTowerNoAx.
Require Import sandbox.ReflectRTowerSmall.

(* -------------------------------------------------------------------- *)
(* Closed arithmetic combinators with explicit de Bruijn-level offsets.  *)
(* -------------------------------------------------------------------- *)

(* This object language uses reversed de Bruijn *levels*: when a term is
   evaluated under [c] ambient binders, the next lambda binder is variable
   [c], and the one after that is [S c].  The [_at c] parameters below
   keep closed combinator templates from accidentally capturing variables
   when they are reused under surrounding lambdas. *)

Definition step_succ_at (c : nat) : term :=
  tLam tpNat (tpArr tpNat tpNat)
       (tLam tpNat tpNat (tApp tS (tVar (S c)))).

Definition double_at (c : nat) : term :=
  tLam tpNat tpNat
       (tApp (tApp (tApp (tNatRec tpNat) (tVar c))
                   (step_succ_at (S c)))
             (tVar c)).

Definition one_term : term := tApp tS tO.

Definition step_double_at (c : nat) : term :=
  tLam tpNat (tpArr tpNat tpNat)
       (tLam tpNat tpNat
             (tApp (double_at (S (S c))) (tVar (S c)))).

Definition pow2_at (c : nat) (n : term) : term :=
  tApp (tApp (tApp (tNatRec tpNat) one_term) (step_double_at c)) n.

Definition pow2_6_term : term := pow2_at 0 (natlit 6).

Definition pow2_1_term : term := pow2_at 0 (natlit 1).

Lemma eval_pow2_6_term :
  eval RTower pow2_6_term = 64.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma eval_pow2_1_term :
  eval RTower pow2_1_term = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma depth_pow2_6_term_eq_17 :
  term_depth pow2_6_term = 17.
Proof. reflexivity. Qed.

Eval vm_compute in (eval RTower pow2_6_term).
Eval vm_compute in (eval RTower pow2_1_term).
Eval vm_compute in (term_depth pow2_6_term).

(* -------------------------------------------------------------------- *)
(* The computed RTower witnesses.                                        *)
(* -------------------------------------------------------------------- *)

Definition witness_rtower_pow2_6 : term :=
  tApp tS (tApp (tApp tRTower (natlit 1)) pow2_6_term).

Lemma eval_witness_rtower_pow2_6 :
  eval RTower witness_rtower_pow2_6 = S (RTower 1 64).
Proof.
  cbv -[RTower]. reflexivity.
Qed.

Definition depth_rtower_pow2_6 : nat :=
  term_depth witness_rtower_pow2_6.

Lemma depth_rtower_pow2_6_eq_19 :
  depth_rtower_pow2_6 = 19.
Proof. reflexivity. Qed.

Eval vm_compute in depth_rtower_pow2_6.

Definition witness_rtower_pow2_1_6 : term :=
  tApp tS (tApp (tApp tRTower pow2_1_term) pow2_6_term).

Lemma eval_witness_rtower_pow2_1_6 :
  eval RTower witness_rtower_pow2_1_6 = S (RTower 2 64).
Proof.
  cbv -[RTower]. reflexivity.
Qed.

Definition depth_rtower_pow2_1_6 : nat :=
  term_depth witness_rtower_pow2_1_6.

Lemma depth_rtower_pow2_1_6_eq_20 :
  depth_rtower_pow2_1_6 = 20.
Proof. reflexivity. Qed.

Eval vm_compute in depth_rtower_pow2_1_6.

Lemma contender_5_lt_RTower_2_64 :
  Contender.contender_5 < RTower 2 64.
Proof.
  eapply Nat.lt_le_trans with (m := RTower 2 48).
  - eapply Nat.lt_trans with (m := RTower 1 45).
    + exact contender_5_lt_RTower_1_45.
    + unfold RTower.
      change 48 with (S (S (S 45))).
      apply (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower_step 1 45).
  - unfold RTower.
    apply (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower_S_d_mono 1 48 64).
    lia.
Qed.

Opaque eval.
Opaque maxBy.

Definition contender_reflect_rtower_computed : nat :=
  largest_RT_nat_of_depth RTower depth_rtower_pow2_1_6.

Lemma contender_reflect_rtower_computed_at_least :
  S (RTower 2 64) <= contender_reflect_rtower_computed.
Proof.
  unfold contender_reflect_rtower_computed, largest_RT_nat_of_depth,
         largest_of_depth.
  rewrite <- eval_witness_rtower_pow2_1_6.
  eapply lowerbound_maxBy with (x := witness_rtower_pow2_1_6).
  - apply termsUpTo_correct. unfold depth_rtower_pow2_1_6. lia.
  - apply eval_tO.
Qed.

Theorem contender_5_lt_reflect_rtower_computed :
  Contender.contender_5 < contender_reflect_rtower_computed.
Proof.
  eapply Nat.lt_le_trans with (m := S (RTower 2 64)).
  - eapply Nat.lt_trans.
    + exact contender_5_lt_RTower_2_64.
    + apply Nat.lt_succ_diag_r.
  - exact contender_reflect_rtower_computed_at_least.
Qed.

Print Assumptions contender_5_lt_reflect_rtower_computed.

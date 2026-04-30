(* Sandbox: Approach D.3 (meta-reflection over the RTower max).

   We already have the second-order reflective language L_RT from
   sandbox/ReflectRTowerSmall.v (and its refinements).  It defines

     largest_RT_nat_of_depth RTower : nat -> nat

   i.e. the depth-bounded maximum of the language that has a primitive
   tRTower interpreted as the reflection tower R_tower.

   This file takes that depth-bounded maximum itself as a new oracle
   prevMax2 : nat -> nat, and applies the one-step reflection trick
   from sandbox/ReflectTowerNoAx again:

     prevMax2 d < largest_reflect_nat_of_depth prevMax2 (d + 3)

   Concretely, we instantiate d with the D.2 computed witness depth
   (which is definitionally 20), so the new reflective max at depth 23
   strictly beats contender_reflect_rtower_computed.

   Compile from the repository root, after the D.2 sandbox modules exist:

     coqc -Q . "" sandbox\ReflectRTower3.v
*)

Require Import Arith Lia.

Require Contender.
Require Import sandbox.ReflectTowerNoAx.
Require Import sandbox.ReflectRTowerComputed.

(* The previous-max oracle for this D.3 step: the D.2 language's own
   depth-bounded maximum function. *)
Definition prevMax2 (d : nat) : nat :=
  sandbox.ReflectRTowerSmall.largest_RT_nat_of_depth
    sandbox.ReflectRTowerSmall.RTower d.

(* Critical: keep the D.2 max/search machinery opaque from *this* file too.
   Otherwise even benign definitional rewrites can trigger kernel conversion
   to run a depth-bounded enumeration during delta-reduction. *)
Opaque sandbox.ReflectRTowerSmall.eval.
Opaque sandbox.ReflectRTowerSmall.maxBy.
Opaque sandbox.ReflectRTowerSmall.termsUpTo.
Opaque sandbox.ReflectRTowerSmall.largest_of_depth.
Opaque sandbox.ReflectRTowerSmall.largest_RT_nat_of_depth.

(* Reflect the D.2 computed depth (definitionally 20), paying +3 depth
   for the unary natlit used by witness_for. *)
Definition depth_reflect_d0 : nat :=
  S (S (S sandbox.ReflectRTowerComputed.depth_rtower_pow2_1_6)).

Definition contender_reflect_rtower3 : nat :=
  sandbox.ReflectTowerNoAx.ReflectTowerNoAx.largest_reflect_nat_of_depth
    prevMax2 depth_reflect_d0.

Eval vm_compute in depth_reflect_d0.

(* The generic one-step reflection lemma, specialized to prevMax2. *)
Lemma prevMax2_lt_reflect : forall d,
  prevMax2 d
  < sandbox.ReflectTowerNoAx.ReflectTowerNoAx.largest_reflect_nat_of_depth
      prevMax2 (S (S (S d))).
Proof.
  intro d.
  unfold sandbox.ReflectTowerNoAx.ReflectTowerNoAx.largest_reflect_nat_of_depth,
         sandbox.ReflectTowerNoAx.ReflectTowerNoAx.largest_of_depth.
  eapply Nat.lt_le_trans
    with (m := sandbox.ReflectTowerNoAx.ReflectTowerNoAx.eval prevMax2
                (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.witness_for d)).
  - rewrite sandbox.ReflectTowerNoAx.ReflectTowerNoAx.eval_witness_for. lia.
  - eapply sandbox.ReflectTowerNoAx.ReflectTowerNoAx.lowerbound_maxBy
      with (x := sandbox.ReflectTowerNoAx.ReflectTowerNoAx.witness_for d).
    + apply sandbox.ReflectTowerNoAx.ReflectTowerNoAx.termsUpTo_correct.
      rewrite sandbox.ReflectTowerNoAx.ReflectTowerNoAx.term_depth_witness_for.
      lia.
    + reflexivity.
Qed.

Theorem contender_reflect_rtower_computed_lt_reflect_rtower3 :
  sandbox.ReflectRTowerComputed.contender_reflect_rtower_computed
  < contender_reflect_rtower3.
Proof.
  unfold contender_reflect_rtower3, depth_reflect_d0.
  change sandbox.ReflectRTowerComputed.contender_reflect_rtower_computed
    with (prevMax2 sandbox.ReflectRTowerComputed.depth_rtower_pow2_1_6).
  apply prevMax2_lt_reflect.
Qed.

Theorem contender_5_lt_reflect_rtower3 :
  Contender.contender_5 < contender_reflect_rtower3.
Proof.
  eapply Nat.lt_trans.
  - exact sandbox.ReflectRTowerComputed.contender_5_lt_reflect_rtower_computed.
  - exact contender_reflect_rtower_computed_lt_reflect_rtower3.
Qed.

Print Assumptions contender_reflect_rtower_computed_lt_reflect_rtower3.
Print Assumptions contender_5_lt_reflect_rtower3.

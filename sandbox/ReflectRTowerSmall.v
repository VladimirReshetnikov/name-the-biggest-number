(* Sandbox: small-witness variant of D.2 (sandbox/ReflectRTower.v).

   Same object language L_RT = STLC + NatRec + tRTower as in
   sandbox/ReflectRTower.v, with two changes:

   * It imports the axiom-free [sandbox.ReflectTowerNoAx] instead of
     [sandbox.ReflectTower].  Combined with using only [tpNat]-typed
     casts in this file's own evaluator (which already only fires
     definitional reductions in [eval_witness_rtower_small]), the result
     is a *fully axiom-free* second-order reflective contender.

   * The witness uses the smallest [K]/[D] pair the [R_tower_step] lemma
     directly produces:  K = 1, D = 45 (i.e. the consequence of
     [R_tower_step 0 42], without the [R_tower_chain]-iterated escalation
     to K = 100, D = 342).  This shrinks the depth budget from 345 to 48
     while still strictly beating [contender_5].

   This is "Phase 1" of the computed-K/D refinement noted in IDEAS.md
   (Approach D.2): no new infrastructure, just the realization that the
   chain lemma's smallest case already suffices.  Phase 2 -- making K
   and/or D themselves *computed* via NatRec, e.g. as powers of two or
   tetration -- is a separate refinement that would shrink the budget
   further but needs a [largest_*_nat_of_depth d]-monotonicity lemma in
   the depth parameter.

   Compile from repo root, after sandbox/ReflectTowerNoAx.vo has been
   built:

     coqc -Q . "" sandbox\ReflectRTowerSmall.v
*)

Require Import Arith Lia.
Require Import List. Import ListNotations.

Require Contender.
Require Import sandbox.ReflectTowerNoAx.

(* Keep the huge enumerations opaque in any conversion checks we trigger. *)
Opaque Contender.largest_STLCNatRec_nat_of_depth.

(* The oracle we reflect: the no-axioms reflection tower.

   Note: we deliberately do NOT mark R_tower itself Opaque here, so that
   the kernel can definitionally reduce [R_tower 0 d] to
   [Contender.largest_STLCNatRec_nat_of_depth d] -- the same trick that
   lets ReflectTowerNoAx.v's main theorem go through.  Inside R_tower's
   recursion the helper [largest_reflect_nat_of_depth] is already opaque
   (made so in ReflectTowerNoAx.v before R_tower_chain), so the kernel
   stops there and never tries to actually run a depth-bounded
   reflective enumeration. *)

Definition RTower : nat -> nat -> nat :=
  sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower.

(* The smallest direct consequence of the step lemma:
     R_tower 0 42  <  R_tower 1 45.
   Same shape as Contender.contender_5 < contender_reflect_tower_7 in
   ReflectTowerNoAx.v, but at the smallest level/depth pair the step
   lemma produces. *)

Lemma contender_5_lt_RTower_1_45 :
  Contender.contender_5 < RTower 1 45.
Proof.
  unfold Contender.contender_5, RTower.
  change (Contender.largest_STLCNatRec_nat_of_depth 42)
    with (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower 0 42).
  change 45 with (S (S (S 42))).
  apply (sandbox.ReflectTowerNoAx.ReflectTowerNoAx.R_tower_step 0 42).
Qed.

(* -------------------------------------------------------------------- *)
(* Pure syntax: types, terms, depths.  Identical to ReflectRTower.v.    *)
(* -------------------------------------------------------------------- *)

Inductive type :=
| tpNat : type
| tpArr : type -> type -> type.

Fixpoint type_eqb (t1 t2 : type) : bool :=
  match t1, t2 with
  | tpNat, tpNat => true
  | tpArr A B, tpArr C D => andb (type_eqb A C) (type_eqb B D)
  | _, _ => false
  end.

Fixpoint type_depth (t : type) : nat :=
  match t with
  | tpNat => 1
  | tpArr t1 t2 => S (max (type_depth t1) (type_depth t2))
  end.

Fixpoint interp_type (tp : type) : Type :=
  match tp with
  | tpNat => nat
  | tpArr t1 t2 => interp_type t1 -> interp_type t2
  end.

Inductive term :=
| tVar (x : nat)
| tLam (A B : type) (body : term)
| tApp (t1 t2 : term)
| tO
| tS
| tNatRec (R : type)
| tRTower.

Definition nat_depth (n : nat) := S n.

Fixpoint term_depth (t : term) : nat :=
  match t with
  | tVar x => S (nat_depth x)
  | tLam A B body => S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
  | tRTower => 1
  end.

Definition lookup {T} (e : list T) (n : nat) : option T :=
  let l := List.length e in if l <=? n then None else nth_error e (l - S n).

Definition error {tp : type} : interp_type tp.
  revert tp.
  refine (fix rec tp := _).
  destruct tp; simpl.
  - exact 0.
  - intros _. apply rec.
Defined.

Definition cast_error (from to : type) :
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
  split; intros; exact error.
Defined.

Definition cast_impl (from to : type) :
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
  revert from to.
  induction from; intros; simpl in *.
  - destruct to; simpl.
    + split; exact id.
    + exact (cast_error tpNat (tpArr to1 to2)).
  - destruct to.
    + exact (cast_error (tpArr from1 from2) tpNat).
    + destruct (type_eqb from1 to1) eqn: E1;
      destruct (type_eqb from2 to2) eqn: E2;
      simpl in *.
      {
        specialize (IHfrom1 to1).
        specialize (IHfrom2 to2).
        destruct IHfrom1 as [F1T1 T1F1].
        destruct IHfrom2 as [F2T2 T2F2].
        split.
        * intros F arg. apply F2T2. apply F. apply T1F1. apply arg.
        * intros F arg. apply T2F2. apply F. apply F1T1. apply arg.
      }
      all: exact (cast_error (tpArr from1 from2) (tpArr to1 to2)).
Defined.

Definition cast {from : type} (to : type) : interp_type from -> interp_type to :=
  fst (cast_impl from to).

Fixpoint interp_term (rt : nat -> nat -> nat)
         (e : list {tp : type & interp_type tp}) (t : term)
  : {tp : type & interp_type tp} :=
  match t with
  | tVar x =>
    match lookup e x with
    | Some R => R
    | None => existT _ tpNat error
    end
  | tLam A B body =>
    existT _ (tpArr A B)
           (fun x' =>
              let r := projT2 (interp_term rt ((existT _ A x') :: e) body) in
              cast B r)
  | tApp t1 t2 =>
    let '(existT _ R1 r1) := interp_term rt e t1 in
    let '(existT _ R2 r2) := interp_term rt e t2 in
    match R1 as R1' return interp_type R1' -> {tp : type & interp_type tp} with
    | tpNat => fun _ => existT _ tpNat error
    | tpArr A B => fun r1 => existT _ B (r1 (cast A r2))
    end r1
  | tO => existT _ tpNat 0
  | tS => existT _ (tpArr tpNat tpNat) S
  | tNatRec R =>
    let r := (@Nat.recursion (interp_type R)) in
    existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R))) r
  | tRTower => existT _ (tpArr tpNat (tpArr tpNat tpNat)) rt
  end.

Definition eval (rt : nat -> nat -> nat) (t : term) : nat :=
  let (tp, res) := interp_term rt nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat         => fun (res : interp_type tpNat) => res
  | tpArr tp1 tp2 => fun (_ : interp_type (tpArr tp1 tp2)) => 0
  end res.

(* -------------------------------------------------------------------- *)
(* Reduction lemmas: only the [tpNat]-restricted [interp_tApp_nat] is
   needed for the witness, and it is definitional.  No FunExt. *)

Lemma interp_tO : forall rt e, interp_term rt e tO = existT _ tpNat 0.
Proof. intros. reflexivity. Qed.

Lemma interp_tS : forall rt e,
    interp_term rt e tS = existT _ (tpArr tpNat tpNat) S.
Proof. intros. reflexivity. Qed.

Lemma interp_tRTower : forall rt e,
    interp_term rt e tRTower = existT _ (tpArr tpNat (tpArr tpNat tpNat)) rt.
Proof. intros. reflexivity. Qed.

Lemma interp_tApp_nat :
  forall rt e t1 t2 B (f : nat -> interp_type B) (a : nat),
    interp_term rt e t1 = existT _ (tpArr tpNat B) f ->
    interp_term rt e t2 = existT _ tpNat a ->
    interp_term rt e (tApp t1 t2) = existT _ B (f a).
Proof.
  intros rt e t1 t2 B f a H1 H2.
  simpl. rewrite H1, H2. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Depth-bounded enumeration (identical to ReflectRTower.v).             *)
(* -------------------------------------------------------------------- *)

Fixpoint typesUpTo (n : nat) : list type :=
  match n with
  | O => []
  | S m =>
    let r := typesUpTo m in
    tpNat :: List.map (fun '(t1, t2) => tpArr t1 t2) (list_prod r r)
  end.

Lemma typesUpTo_correct : forall n t,
    type_depth t <= n <-> List.In t (typesUpTo n).
Proof.
  induction n; intros; split; intros.
  - destruct t; simpl in *; lia.
  - simpl in *. contradiction.
  - simpl. destruct t; [auto|].
    right. simpl in *.
    match goal with
    | |- In ?e (map ?f _) => change e with (f (t1, t2))
    end.
    apply in_map.
    apply in_prod; eapply IHn; lia.
  - simpl in *. destruct H.
    + subst. simpl. lia.
    + apply in_map_iff in H.
      destruct H as [[t1 t2] [? H]].
      subst t.
      apply in_prod_iff in H.
      destruct H as [H1 H2].
      pose proof ((proj2 (IHn _)) H1).
      pose proof ((proj2 (IHn _)) H2).
      simpl. lia.
Qed.

Fixpoint natsUpTo (n : nat) : list nat :=
  match n with
  | O => []
  | S m => m :: natsUpTo m
  end.

Lemma natsUpTo_correct : forall n m,
    nat_depth m <= n <-> List.In m (natsUpTo n).
Proof.
  induction n; intros; unfold nat_depth in *; split; intros; simpl in *.
  - exfalso. lia.
  - contradiction.
  - assert (n = m \/ S m <= n) as C by lia.
    destruct C as [C | C]; firstorder idtac.
  - destruct H.
    + lia.
    + specialize (IHn m). apply proj2 in IHn. specialize (IHn H). lia.
Qed.

Fixpoint termsUpTo (n : nat) : list term :=
  match n with
  | O => []
  | S m =>
    List.map tVar (natsUpTo m) ++
    List.map (fun '(A, B, body) => tLam A B body)
             (list_prod (list_prod (typesUpTo m) (typesUpTo m)) (termsUpTo m)) ++
    List.map (fun '(t1, t2) => tApp t1 t2)
             (list_prod (termsUpTo m) (termsUpTo m)) ++
    [tO] ++ [tS] ++
    List.map tNatRec (typesUpTo m) ++
    [tRTower]
  end.

Lemma termsUpTo_correct : forall n t,
    term_depth t <= n <-> List.In t (termsUpTo n).
Proof.
  induction n; intros; split; intros.
  - destruct t; simpl in *; lia.
  - simpl in *. contradiction.
  - destruct t; simpl in *.
    + do 0 (apply in_or_app; right). apply in_or_app; left.
      apply in_map. apply natsUpTo_correct. lia.
    + do 1 (apply in_or_app; right). apply in_or_app; left.
      match goal with
      | |- In ?e (map ?f _) => change e with (f (A, B, t))
      end.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia ].
    + do 2 (apply in_or_app; right). apply in_or_app; left.
      match goal with
      | |- In ?e (map ?f _) => change e with (f (t1, t2))
      end.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia ].
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. right. right.
      apply in_or_app. left.
      apply in_map. apply (proj1 (typesUpTo_correct _ _)). lia.
    + do 3 (apply in_or_app; right). simpl. right. right.
      apply in_or_app. right. simpl. auto.
  - simpl in *.
    repeat ((simpl in H || apply in_app_iff in H || idtac); destruct H).
    + apply in_map_iff in H.
      destruct H as [x [? H]].
      subst t.
      pose proof ((proj2 (natsUpTo_correct _ _)) H).
      simpl. lia.
    + apply in_map_iff in H.
      destruct H as [[[A B] body] [? H]].
      subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H1).
      pose proof ((proj2 (IHn _)) H0).
      simpl. lia.
    + apply in_map_iff in H.
      destruct H as [[t1 t2] [? H]].
      subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (IHn _)) H).
      pose proof ((proj2 (IHn _)) H0).
      simpl. lia.
    + simpl. lia.
    + simpl. lia.
    + apply in_map_iff in H.
      destruct H as [R [? H]].
      subst t.
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      simpl. lia.
    + simpl. lia.
Qed.

Opaque termsUpTo.

(* -------------------------------------------------------------------- *)
(* maxBy and the depth-bounded maximum (identical to ReflectRTower.v).   *)
(* -------------------------------------------------------------------- *)

Fixpoint maxBy {T : Type} (f : T -> nat) (currentMax : nat)
         (currentBest : T) (l : list T) : T :=
  match l with
  | nil => currentBest
  | cons h t =>
    if currentMax <? (f h) then
      maxBy f (f h) h t
    else
      maxBy f currentMax currentBest t
  end.

Lemma maxBy_at_least_currentMax {T : Type} :
  forall (f : T -> nat) l currentMax currentBest,
    f currentBest = currentMax ->
    currentMax <= f (maxBy f currentMax currentBest l).
Proof.
  induction l; intros; simpl in *.
  - lia.
  - subst. destruct (f currentBest <? f a) eqn: E.
    + apply Nat.ltb_lt in E.
      specialize (IHl (f a) _ eq_refl). lia.
    + apply Nat.ltb_ge in E.
      eapply IHl. reflexivity.
Qed.

Lemma lowerbound_maxBy {T : Type} :
  forall (f : T -> nat) x l currentMax currentBest,
    List.In x l ->
    f currentBest = currentMax ->
    f x <= f (maxBy f currentMax currentBest l).
Proof.
  induction l; intros; simpl in *.
  - contradiction.
  - destruct H.
    + subst.
      destruct (f currentBest <? f x) eqn: E.
      * apply Nat.ltb_lt in E.
        eapply maxBy_at_least_currentMax. reflexivity.
      * apply Nat.ltb_ge in E.
        eapply Nat.le_trans. 1: eassumption.
        eapply maxBy_at_least_currentMax. reflexivity.
    + subst currentMax.
      destruct (f currentBest <? f a) eqn: E.
      * exact (IHl (f a) a H eq_refl).
      * exact (IHl (f currentBest) currentBest H eq_refl).
Qed.

Definition largest_of_depth (rt : nat -> nat -> nat) (n : nat) : term :=
  maxBy (eval rt) 0 tO (termsUpTo n).

Definition largest_RT_nat_of_depth (rt : nat -> nat -> nat) (n : nat) : nat :=
  eval rt (largest_of_depth rt n).

(* -------------------------------------------------------------------- *)
(* Witness: K = 1, D = 45, both unary.                                   *)
(* -------------------------------------------------------------------- *)

Fixpoint natlit (n : nat) : term :=
  match n with
  | O => tO
  | S n' => tApp tS (natlit n')
  end.

Lemma term_depth_natlit : forall n, term_depth (natlit n) = S n.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn. lia.
Qed.

Lemma interp_natlit : forall rt n,
    interp_term rt nil (natlit n) = existT _ tpNat n.
Proof.
  intros rt. induction n.
  - apply interp_tO.
  - simpl natlit.
    apply (interp_tApp_nat rt nil tS (natlit n) tpNat S n).
    + apply interp_tS.
    + exact IHn.
Qed.

(* The witness term  S (tRTower 1 45)  evaluates to  S (RTower 1 45). *)

Definition witness_rtower_small : term :=
  tApp tS (tApp (tApp tRTower (natlit 1)) (natlit 45)).

Lemma interp_witness_rtower_small :
    interp_term RTower nil witness_rtower_small
    = existT _ tpNat (S (RTower 1 45)).
Proof.
  unfold witness_rtower_small.
  apply (interp_tApp_nat RTower nil tS
                          (tApp (tApp tRTower (natlit 1)) (natlit 45))
                          tpNat S (RTower 1 45)).
  - apply interp_tS.
  - apply (interp_tApp_nat RTower nil
                            (tApp tRTower (natlit 1)) (natlit 45)
                            tpNat (RTower 1) 45).
    + apply (interp_tApp_nat RTower nil tRTower (natlit 1)
                              (tpArr tpNat tpNat) RTower 1).
      * apply interp_tRTower.
      * apply interp_natlit.
    + apply interp_natlit.
Qed.

Lemma eval_witness_rtower_small :
  eval RTower witness_rtower_small = S (RTower 1 45).
Proof.
  unfold eval. rewrite interp_witness_rtower_small. reflexivity.
Qed.

Lemma eval_tO : forall rt, eval rt tO = 0.
Proof. intro rt. reflexivity. Qed.

(* The depth budget for this small witness is 48. *)

Definition depth_rtower_small : nat := term_depth witness_rtower_small.

Lemma depth_rtower_small_eq_48 : depth_rtower_small = 48.
Proof. reflexivity. Qed.

Eval vm_compute in depth_rtower_small.

(* Make eval / maxBy opaque before defining the contender. *)
Opaque eval.
Opaque maxBy.

Definition contender_reflect_rtower_small : nat :=
  largest_RT_nat_of_depth RTower depth_rtower_small.

Lemma contender_reflect_rtower_small_at_least :
  S (RTower 1 45) <= contender_reflect_rtower_small.
Proof.
  unfold contender_reflect_rtower_small, largest_RT_nat_of_depth, largest_of_depth.
  rewrite <- eval_witness_rtower_small.
  eapply lowerbound_maxBy with (x := witness_rtower_small).
  - apply termsUpTo_correct. unfold depth_rtower_small. lia.
  - apply eval_tO.
Qed.

Theorem contender_5_lt_reflect_rtower_small :
  Contender.contender_5 < contender_reflect_rtower_small.
Proof.
  eapply Nat.lt_le_trans with (m := S (RTower 1 45)).
  - eapply Nat.lt_trans.
    + exact contender_5_lt_RTower_1_45.
    + apply Nat.lt_succ_diag_r.
  - exact contender_reflect_rtower_small_at_least.
Qed.

Print Assumptions contender_5_lt_reflect_rtower_small.

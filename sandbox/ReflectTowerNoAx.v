(* Sandbox: no-axioms variant of sandbox/ReflectTower.v.

   ReflectTower.v imports FunctionalExtensionality.  The axiom is used
   *only* through [cast_impl_same -> cast_same -> interp_tApp].  The witness
   chain we actually care about

       eval_witness_for : eval prev (witness_for n) = S (prev n)

   feeds [interp_tApp] only with [A = tpNat]-typed arguments, where
   [cast tpNat a = a] is *definitional*: [cast_impl tpNat tpNat] reduces to
   [(id, id)] without any extensionality detour.  So a restricted form of
   [interp_tApp] is enough, and the FunExt import drops out entirely.

   The eliminations:
     * remove [Require Import FunctionalExtensionality]
     * remove [cast_impl_same], [cast_same]
     * remove [interp_tLam]      (* it would still need FunExt; unused here *)
     * replace [interp_tApp] with [interp_tApp_nat] (specialised to tpNat)

   Same end-state theorem:

     Theorem contender_5_lt_reflect_tower_7 :
       Contender.contender_5 < contender_reflect_tower_7.

   with [contender_reflect_tower_7 := R_tower 100 342] and

     Print Assumptions contender_5_lt_reflect_tower_7.
       (Closed under the global context.)

   Compile from repo root, after Contender.vo has been built:

     coqc -Q . "" sandbox\ReflectTowerNoAx.v
*)

Require Import Arith Lia.
Require Import List. Import ListNotations.

Require Contender.

Opaque Contender.largest_STLCNatRec_nat_of_depth.

Module ReflectTowerNoAx.

(* -------------------------------------------------------------------- *)
(* Pure syntax: types, terms, depths -- identical to ReflectTower.v.    *)
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
| tPrevMax.

Definition nat_depth (n : nat) := S n.

Fixpoint term_depth (t : term) : nat :=
  match t with
  | tVar x => S (nat_depth x)
  | tLam A B body => S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
  | tPrevMax => 1
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

(* The single non-trivial reduction fact about [cast] we need: when source
   *and* target are both tpNat, the cast is the identity.  This is
   *definitional* -- no extensionality, no [cast_impl_same]. *)

Lemma cast_nat_id : forall (a : nat), @cast tpNat tpNat a = a.
Proof. intro a. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(* Section: parameterized interpreter (identical to ReflectTower.v).    *)
(* -------------------------------------------------------------------- *)

Section Reflect.
Context (prevMax : nat -> nat).

Definition interp_term :
  forall (e : list {tp : type & interp_type tp}) (t : term),
    {tp : type & interp_type tp}.
  refine (fix rec e t {struct t} :=
    match t with
    | tVar x => _
    | tLam A B body => _
    | tApp t1 t2 => _
    | tO => _
    | tS => _
    | tNatRec R => _
    | tPrevMax => _
    end).
  - destruct (lookup e x) as [R|].
    + exact R.
    + exact (existT _ tpNat error).
  - refine (existT _ (tpArr A B) _).
    intro x'.
    set (r := projT2 (rec ((existT _ A x') :: e) body)).
    exact (cast B r).
  - destruct (rec e t1) as [R1 r1].
    destruct (rec e t2) as [R2 r2].
    destruct R1 as [|A B]; [exact (existT _ tpNat error)|].
    exact (existT _ B (r1 (cast A r2))).
  - exact (existT _ tpNat 0).
  - exact (existT _ (tpArr tpNat tpNat) S).
  - exact (existT _
                  (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R)))
                  (@Nat.recursion (interp_type R))).
  - exact (existT _ (tpArr tpNat tpNat) prevMax).
Defined.

Definition eval (t : term) : nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return interp_type t0 -> nat with
  | tpNat => fun res : interp_type tpNat => res
  | tpArr _ _ => fun _ => 0
  end res.

(* Reduction lemmas.  We keep [interp_tO], [interp_tS], [interp_tPrevMax]
   exactly as before -- they are definitional.  Crucially we do NOT keep
   [interp_tLam] (which would force FunExt) and we replace [interp_tApp]
   with the tpNat-specialised version below. *)

Lemma interp_tO : forall e, interp_term e tO = existT _ tpNat 0.
Proof. intros. reflexivity. Qed.

Lemma interp_tS : forall e, interp_term e tS = existT _ (tpArr tpNat tpNat) S.
Proof. intros. reflexivity. Qed.

Lemma interp_tPrevMax : forall e,
  interp_term e tPrevMax = existT _ (tpArr tpNat tpNat) prevMax.
Proof. intros. reflexivity. Qed.

(* The restricted application lemma.  Same statement as [interp_tApp] but
   with [A] forced to be [tpNat], for which [cast tpNat _ = id] holds
   definitionally, so the proof is trivial. *)

Lemma interp_tApp_nat :
  forall e t1 t2 B (f : nat -> interp_type B) (a : nat),
    interp_term e t1 = existT _ (tpArr tpNat B) f ->
    interp_term e t2 = existT _ tpNat a ->
    interp_term e (tApp t1 t2) = existT _ B (f a).
Proof.
  intros e t1 t2 B f a H1 H2.
  simpl.
  rewrite H1, H2.
  reflexivity.
Qed.

End Reflect.

(* -------------------------------------------------------------------- *)
(* Enumeration (identical to ReflectTower.v).                            *)
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
    change (tpArr t1 t2) with ((fun '(t1, t2) => tpArr t1 t2) (t1, t2)).
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
    [tPrevMax]
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
      change (tLam A B t) with
        ((fun '(A, B, body) => tLam A B body) ((A, B), t)).
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia].
    + do 2 (apply in_or_app; right). apply in_or_app; left.
      change (tApp t1 t2) with ((fun '(t1, t2) => tApp t1 t2) (t1, t2)).
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (IHn _))
             | lia].
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. right. right.
      apply in_or_app; left. apply in_map. apply typesUpTo_correct. lia.
    + do 3 (apply in_or_app; right). simpl. right. right.
      apply in_or_app; right. simpl. auto.
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
    + subst. simpl. lia.
Qed.

(* -------------------------------------------------------------------- *)
(* maxBy and largest_of_depth (identical to ReflectTower.v).             *)
(* -------------------------------------------------------------------- *)

Fixpoint maxBy {T : Type} (f : T -> nat) (currentMax : nat)
         (currentBest : T) (l : list T) : T :=
  match l with
  | nil => currentBest
  | cons h t =>
    if currentMax <? f h then
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
    + subst.
      destruct (f currentBest <? f a) eqn: E.
      * apply Nat.ltb_lt in E. eauto.
      * apply Nat.ltb_ge in E. eauto.
Qed.

Definition largest_of_depth (prevMax : nat -> nat) (n : nat) : term :=
  maxBy (eval prevMax) 0 tO (termsUpTo n).

Definition largest_reflect_nat_of_depth (prevMax : nat -> nat) (n : nat) : nat :=
  eval prevMax (largest_of_depth prevMax n).

(* -------------------------------------------------------------------- *)
(* Witness machinery: unary literal and the witness term.               *)
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

Definition witness_for (n : nat) : term :=
  tApp tS (tApp tPrevMax (natlit n)).

Lemma term_depth_witness_for : forall n, term_depth (witness_for n) = S (S (S n)).
Proof.
  intro n. unfold witness_for. simpl.
  rewrite term_depth_natlit. lia.
Qed.

(* The same chain as in ReflectTower.v, but using [interp_tApp_nat]. *)

Lemma interp_natlit : forall prev n,
  interp_term prev nil (natlit n) = existT _ tpNat n.
Proof.
  intros prev. induction n.
  - apply interp_tO.
  - simpl natlit.
    apply (interp_tApp_nat prev nil tS (natlit n) tpNat S n).
    + apply interp_tS.
    + exact IHn.
Qed.

Lemma interp_witness_for : forall prev n,
  interp_term prev nil (witness_for n) = existT _ tpNat (S (prev n)).
Proof.
  intros. unfold witness_for.
  apply (interp_tApp_nat prev nil tS (tApp tPrevMax (natlit n))
                          tpNat S (prev n)).
  - apply interp_tS.
  - apply (interp_tApp_nat prev nil tPrevMax (natlit n)
                            tpNat prev n).
    + apply interp_tPrevMax.
    + apply interp_natlit.
Qed.

Lemma eval_witness_for : forall prev n,
  eval prev (witness_for n) = S (prev n).
Proof.
  intros. unfold eval.
  rewrite interp_witness_for. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* The reflection tower (identical to ReflectTower.v).                   *)
(* -------------------------------------------------------------------- *)

Fixpoint R_tower (k : nat) : nat -> nat :=
  match k with
  | 0    => Contender.largest_STLCNatRec_nat_of_depth
  | S k' => largest_reflect_nat_of_depth (R_tower k')
  end.

Lemma R_tower_step : forall (k d : nat),
  R_tower k d < R_tower (S k) (S (S (S d))).
Proof.
  intros k d.
  unfold R_tower at 2. fold R_tower.
  unfold largest_reflect_nat_of_depth, largest_of_depth.
  eapply Nat.lt_le_trans
    with (m := eval (R_tower k) (witness_for d)).
  - rewrite eval_witness_for. lia.
  - eapply lowerbound_maxBy with (x := witness_for d).
    + apply termsUpTo_correct.
      rewrite term_depth_witness_for. lia.
    + reflexivity.
Qed.

Opaque largest_reflect_nat_of_depth.
Opaque eval.
Opaque termsUpTo.
Opaque maxBy.

Lemma R_tower_chain :
  forall n, R_tower 0 42 < R_tower (S n) (3 * (S n) + 42).
Proof.
  induction n.
  - replace (3 * S 0 + 42) with (S (S (S 42))) by lia.
    apply (R_tower_step 0 42).
  - eapply Nat.lt_trans.
    + exact IHn.
    + replace (3 * S (S n) + 42)
        with (S (S (S (3 * S n + 42)))) by lia.
      apply R_tower_step.
Qed.

(* -------------------------------------------------------------------- *)
(* Main theorem: same end-state as ReflectTower.v, no axioms.            *)
(* -------------------------------------------------------------------- *)

Definition contender_reflect_tower_7 : nat := R_tower 100 342.

Theorem contender_5_lt_reflect_tower_7 :
  Contender.contender_5 < contender_reflect_tower_7.
Proof.
  unfold contender_reflect_tower_7.
  unfold Contender.contender_5.
  change (Contender.largest_STLCNatRec_nat_of_depth 42) with (R_tower 0 42).
  change 342 with (3 * S 99 + 42).
  apply (R_tower_chain 99).
Qed.

Print Assumptions contender_5_lt_reflect_tower_7.

End ReflectTowerNoAx.

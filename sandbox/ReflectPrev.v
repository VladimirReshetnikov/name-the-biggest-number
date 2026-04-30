(* Sandbox: one-level reflective extension of the current contender language.

   This is intentionally exploratory.  The question is whether the
   "reflection primitive" idea is merely a depth-saving trick or whether it
   gives a clean next-contender architecture.  We extend STLC+NatRec with

     tPrevMax : Nat -> Nat

   interpreted as Contender.largest_STLCNatRec_nat_of_depth.  Then the term

     S (tPrevMax 42)

   is an internal witness that a depth-bounded search in the extended language
   beats contender_5.  The point of this file is not to propose this as the
   final answer yet, but to make the bookkeeping concrete and mechanically
   reusable. *)

Require Import Arith Lia.
Require Import List. Import ListNotations.

Require Contender.

Module ReflectPrev.

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
  - exact (existT _ (tpArr tpNat tpNat)
                  Contender.largest_STLCNatRec_nat_of_depth).
Defined.

Definition eval (t : term) : nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return interp_type t0 -> nat with
  | tpNat => fun res : interp_type tpNat => res
  | tpArr _ _ => fun _ => 0
  end res.

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

Definition largest_of_depth (n : nat) : term := maxBy eval 0 tO (termsUpTo n).
Definition largest_reflect_nat_of_depth (n : nat) : nat := eval (largest_of_depth n).

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

Fixpoint natlit (n : nat) : term :=
  match n with
  | O => tO
  | S n' => tApp tS (natlit n')
  end.

Definition t42 : term := natlit 42.

Definition reflect_witness : term :=
  tApp tS (tApp tPrevMax t42).

Eval vm_compute in (term_depth reflect_witness).

Lemma eval_reflect_witness :
  eval reflect_witness = S Contender.contender_5.
Proof.
  unfold reflect_witness, t42.
  unfold Contender.contender_5.
  cbv -[Contender.largest_STLCNatRec_nat_of_depth].
  reflexivity.
Qed.

Definition contender_reflect_6 : nat := largest_reflect_nat_of_depth 45.

Theorem contender_5_lt_reflect_6 :
  Contender.contender_5 < contender_reflect_6.
Proof.
  unfold contender_reflect_6, largest_reflect_nat_of_depth, largest_of_depth.
  eapply Nat.lt_le_trans with (m := eval reflect_witness).
  - rewrite eval_reflect_witness. lia.
  - eapply lowerbound_maxBy with (x := reflect_witness).
    + eapply termsUpTo_correct. cbv. lia.
    + reflexivity.
Qed.

Print Assumptions contender_5_lt_reflect_6.

End ReflectPrev.

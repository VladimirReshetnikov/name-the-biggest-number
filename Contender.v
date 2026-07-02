Require Import Arith Lia.


Fixpoint iter (f : nat -> nat) (b : nat) :=
  match b with
  | 0 => 1
  | S b' => f (iter f b')
  end.

Fixpoint ack (n a b : nat) :=
  match n with
  | 0 => S b
  | 1 => a + b
  | S n' => iter (ack n' a) b
  end.


(* This is the previous contender for largest number *)
(* Submitted by codyroux *)
Definition contender_4 := ack 5 42 10002.


Require Import List. Import ListNotations.


(* Definition of the language STLC+NatRec: *)

Inductive type :=
| tpNat: type
| tpArr: type -> type -> type.

Fixpoint type_eqb(t1 t2: type): bool :=
  match t1, t2 with
  | tpNat, tpNat => true
  | tpArr A B, tpArr C D => andb (type_eqb A C) (type_eqb B D)
  | _, _ => false
  end.

Fixpoint type_depth(t: type): nat :=
  match t with
  | tpNat => 1
  | tpArr t1 t2 => S (max (type_depth t1) (type_depth t2))
  end.

Fixpoint interp_type(tp: type): Type :=
  match tp with
  | tpNat => nat
  | tpArr t1 t2 => (interp_type t1) -> (interp_type t2)
  end.

Inductive term :=
| tVar(x: nat) (* 0 = last element of the env, ie the outermost binder (reversed DeBruijn) *)
| tLam(A B: type)(body: term)
| tApp(t1 t2: term)
| tO
| tS
| tNatRec(R: type).

Definition nat_depth(n: nat) := S n.

Fixpoint term_depth(t: term): nat :=
  match t with
  | tVar x => S (nat_depth x)
  | tLam A B body => S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
  end.

Definition lookup{T}(e: list T)(n: nat): option T :=
  let l := List.length e in if l <=? n then None else nth_error e (l - S n).

Goal lookup [10; 11; 12] 0 = Some 12. reflexivity. Qed.
Goal lookup [10; 11; 12] 1 = Some 11. reflexivity. Qed.
Goal lookup [10; 11; 12] 2 = Some 10. reflexivity. Qed.
Goal lookup [10; 11; 12] 3 = None. reflexivity. Qed.

Definition error{tp: type}: interp_type tp.
  revert tp.
  refine (fix rec tp := _).
  destruct tp; simpl.
  - exact 0.
  - intros _. apply rec.
Defined.

Definition cast_error(from to: type):
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
  split; intros; exact error.
Defined.

Definition cast_impl(from to: type):
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

(* designed to be computable (no opaque proofs) *)
Definition cast{from: type}(to: type): interp_type from -> interp_type to :=
  fst (cast_impl from to).

Definition interp_term: forall (e: list {tp: type & interp_type tp}) (t: term),
    {tp: type & interp_type tp}.
  refine (fix rec e t {struct t} :=
  match t with
  | tVar x => _
  | tLam A B body => _
  | tApp t1 t2 => _
  | tO => _
  | tS => _
  | tNatRec R => _
  end).
  - destruct (lookup e x) as [R|].
    + exact R.
    + exact (existT _ tpNat error).
  - refine (existT _ (tpArr A B) _).
    simpl.
    intro x'.
    set (r := (projT2 (rec ((existT _ A x') :: e) body))).
    simpl in r.
    exact (cast B r).
  - destruct (rec e t1) as [R1 r1] eqn: E1.
    destruct (rec e t2) as [R2 r2] eqn: E2.
    destruct R1 as [|A B]; [exact (existT _ tpNat error)|].
    simpl in *.
    exact (existT _ _ (r1 (cast A r2))).
  - exact (existT _ tpNat 0).
  - exact (existT _ (tpArr tpNat tpNat) S).
  - set (r := (@Nat.recursion (interp_type R))).
    exact (existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R))) r).
Defined.


(* Defining the new contender: *)

Fixpoint typesUpTo(n: nat): list type :=
  match n with
  | O => []
  | S m =>
    let r := typesUpTo m in
    tpNat :: List.map (fun '(t1, t2) => tpArr t1 t2) (list_prod r r)
  end.

Lemma typesUpTo_correct: forall n t,
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
      simpl.
      lia.
Qed.

Fixpoint natsUpTo(n: nat): list nat :=
  match n with
  | O => []
  | S m => m :: natsUpTo m
  end.

Lemma natsUpTo_correct: forall n m,
    nat_depth m <= n <-> List.In m (natsUpTo n).
Proof.
  induction n; intros; unfold nat_depth in *; split; intros; simpl in *.
  - exfalso. lia.
  - contradiction.
  - assert (n = m \/ S m <= n) as C by lia. destruct C as [C | C]; firstorder idtac.
  - destruct H.
    + lia.
    + specialize (IHn m). apply proj2 in IHn. specialize (IHn H). lia.
Qed.

Fixpoint termsUpTo(n: nat): list term :=
  match n with
  | O => []
  | S m =>
    List.map tVar (natsUpTo m) ++
    List.map (fun '(A, B, body) => tLam A B body)
             (list_prod (list_prod (typesUpTo m) (typesUpTo m)) (termsUpTo m)) ++
    List.map (fun '(t1, t2) => tApp t1 t2)
             (list_prod (termsUpTo m) (termsUpTo m)) ++
    [tO] ++ [tS] ++
    List.map tNatRec (typesUpTo m)
  end.

Lemma termsUpTo_correct: forall n t,
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
             | lia].
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
             | lia].
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. right. right.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia].
  - simpl in *.
    repeat ((simpl in H || apply in_app_iff in H || idtac); destruct H).
    + apply in_map_iff in H.
      destruct H as [x [? H]].
      subst t.
      pose proof ((proj2 (natsUpTo_correct _ _)) H).
      simpl.
      lia.
    + apply in_map_iff in H.
      destruct H as [[[A B] body] [? H]].
      subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H1).
      pose proof ((proj2 (IHn _)) H0).
      simpl.
      lia.
    + apply in_map_iff in H.
      destruct H as [[t1 t2] [? H]].
      subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (IHn _)) H).
      pose proof ((proj2 (IHn _)) H0).
      simpl.
      lia.
    + simpl. lia.
    + simpl. lia.
    + apply in_map_iff in H.
      destruct H as [R [? H]].
      subst t.
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      simpl.
      lia.
Qed.

Definition eval(t : term): nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat         => fun (res: interp_type tpNat) => res
  | tpArr tp1 tp2 => fun (res: interp_type (tpArr tp1 tp2)) => 0
  end res.

Fixpoint maxBy{T: Type}(f: T -> nat)(currentMax: nat)(currentBest: T)(l: list T): T :=
  match l with
  | nil => currentBest
  | cons h t =>
    if currentMax <? (f h) then
      maxBy f (f h) h t
    else
      maxBy f currentMax currentBest t
  end.

Definition largest_of_depth(n: nat): term := maxBy eval 0 tO (termsUpTo n).

Eval vm_compute in (largest_of_depth 1).
Eval vm_compute in (largest_of_depth 2).
Eval vm_compute in (largest_of_depth 3).
Eval vm_compute in (largest_of_depth 4).

Definition largest_STLCNatRec_nat_of_depth(n: nat): nat := eval (largest_of_depth n).

(* Small examples are computable: *)
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 1).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 2).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 3).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 4).
(* but as soon as it would get interesting, it becomes too inefficient *)


(* This is the current contender for largest number *)
(* Submitted by samuelgruetter *)
(* <brag>Note how its definition does not require any large literals</brag> ;-) *)
Definition contender_5: nat := largest_STLCNatRec_nat_of_depth 42.


(* Reification automation: *)

Definition type_eq_dec: forall x y : type, {x = y} + {x <> y}.
  induction x; destruct y eqn: E; intros; simpl.
  - left. reflexivity.
  - right. intro C. discriminate.
  - right. intro C. discriminate.
  - specialize (IHx1 t1).
    specialize (IHx2 t2).
    destruct IHx1 as [E1 | N1]; destruct IHx2 as [E2 | N2]; try (right; congruence).
    left. subst. reflexivity.
Defined.

Lemma type_eqb_true: forall t1 t2, type_eqb t1 t2 = true -> t1 = t2.
Proof.
  induction t1; intros; destruct t2; simpl in *; try congruence.
  apply Bool.andb_true_iff in H. destruct H. f_equal; eauto.
Qed.

Lemma type_eqb_same: forall t, type_eqb t t = true.
Proof.
  induction t; simpl.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(* only for the reification machinery, will not show up in the final proof *)
Require Import FunctionalExtensionality.

Lemma cast_impl_same: forall (B: type) (t: interp_type B),
    fst (cast_impl B B) t = t /\ snd (cast_impl B B) t = t.
Proof.
  induction B; intros; simpl; unfold id.
  - auto.
  - do 2 rewrite type_eqb_same.
    destruct (cast_impl B1 B1) as [fw1 bw1] eqn: E1.
    destruct (cast_impl B2 B2) as [fw2 bw2] eqn: E2.
    simpl in *.
    split; extensionality arg.
    + specialize (IHB1 arg).
      apply proj2 in IHB1.
      rewrite IHB1.
      specialize (IHB2 (t arg)).
      apply proj1 in IHB2.
      exact IHB2.
    + specialize (IHB1 arg).
      apply proj1 in IHB1.
      rewrite IHB1.
      specialize (IHB2 (t arg)).
      apply proj2 in IHB2.
      exact IHB2.
Qed.

Lemma cast_same: forall (B: type) (t: interp_type B),
    cast B t = t.
Proof.
  intros. unfold cast.
  pose proof (cast_impl_same B t) as P.
  apply proj1 in P.
  exact P.
Qed.

Lemma interp_tVar: forall e x (p: {tp: type & interp_type tp}),
    lookup e x = Some p ->
    interp_term e (tVar x) = p.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma interp_tVar_head: forall e y (p: {tp: type & interp_type tp}),
    y = List.length e ->
    interp_term (p :: e) (tVar y) = p.
Proof.
  intros. subst. simpl. unfold lookup, List.find.
  change (length (p :: e)) with (S (length e)).
  destruct (S (length e) <=? length e) eqn: E. {
    apply Nat.leb_le in E. exfalso. lia.
  }
  rewrite Nat.sub_diag.
  reflexivity.
Qed.

Lemma interp_tVar_tail: forall e y (p1 p2: {tp: type & interp_type tp}),
    length e <=? y = false ->
    interp_term e (tVar y) = p2 ->
    interp_term (p1 :: e) (tVar y) = p2.
Proof.
  intros. simpl in *. unfold lookup, List.find in *.
  change (length (p1 :: e)) with (S (length e)).
  rewrite H in H0.
  apply Nat.leb_gt in H.
  replace (S (length e) - S y) with (S (length e - S y)) by lia.
  destruct (S (length e) <=? y) eqn: E. {
    apply Nat.leb_le in E. exfalso. lia.
  }
  simpl.
  assumption.
Qed.

Lemma interp_tLam: forall e A B body f,
  (forall x0, interp_term (existT interp_type A x0 :: e) body = existT _ B (f x0)) ->
  interp_term e (tLam A B body) = existT _ (tpArr A B) f.
Proof.
  simpl.
  intros.
  f_equal.
  extensionality x'.
  specialize (H x').
  destruct (interp_term (existT interp_type A x' :: e) body) eqn: E.
  inversion H.
  subst.
  simpl.
  apply cast_same.
Qed.

Lemma interp_tApp: forall e t1 t2 A B (f: interp_type A -> interp_type B) (a: interp_type A),
    interp_term e t1 = existT _ (tpArr A B) f ->
    interp_term e t2 = existT _ A a ->
    interp_term e (tApp t1 t2) = existT _ B (f a).
Proof.
  intros.
  simpl.
  destruct (interp_term e t1) eqn: E1.
  destruct (interp_term e t2) eqn: E2.
  pose proof (EqdepFacts.eq_sigT_fst H). subst x.
  apply Eqdep_dec.inj_pair2_eq_dec in H. 2: apply type_eq_dec. subst i.
  pose proof (EqdepFacts.eq_sigT_fst H0). subst x0.
  apply Eqdep_dec.inj_pair2_eq_dec in H0. 2: apply type_eq_dec. subst i0.
  rewrite cast_same.
  reflexivity.
Qed.

Lemma interp_tO: forall e, interp_term e tO = existT _ tpNat 0.
Proof. intros. reflexivity. Qed.

Lemma interp_tS: forall e, interp_term e tS = existT _ (tpArr tpNat tpNat) S.
Proof. intros. reflexivity. Qed.

Lemma interp_tNatRec: forall e R,
    interp_term e (tNatRec R) =
    existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R)))
           (@Nat.recursion (interp_type R)).
Proof.
  intros. subst. reflexivity.
Qed.

(*
Notation "A --> B" := (tpArr A B) (at level 60, right associativity).
*)

Ltac reify_type T :=
  lazymatch T with
  | ?A -> ?B => let A' := reify_type A in
                let B' := reify_type B in
                constr:(tpArr A' B')
  | nat => constr:(tpNat)
  | interp_type ?A => constr:(A)
  | _ => fail "" T "is not a type"
  end.

Ltac t :=
  lazymatch goal with
  | |- interp_term ?e ?t = existT _ ?T (fun _ => _) =>
    eapply interp_tLam; intros ?
  | |- interp_term ?e ?t = existT _ ?T O =>
    eapply interp_tO
  | |- interp_term ?e ?t = existT _ ?T S =>
    eapply interp_tS
  | |- interp_term ?e ?t = existT _ ?T Nat.recursion =>
    eapply interp_tNatRec
  | |- interp_term ?e ?t = existT _ ?B (?f ?a) =>
    let A := type of a in
    let A := eval cbv beta iota in A in
    let A := reify_type A in
    eapply (interp_tApp e _ _ A B)
  | |- interp_term ?e ?t = existT _ ?T ?x =>
    is_var x;
    first [ eapply interp_tVar_head; cbv [length]; reflexivity
          | eapply interp_tVar_tail; cbv [length]]
  end.


(* Expressing contender_4 as an STLC+NatRec term: *)

Definition ack'(n: nat): nat -> nat -> nat :=
  Nat.recursion
    (fun a b => S b)
    (fun (pred0: nat) (rec0: nat -> nat -> nat) =>
       Nat.recursion
         (Nat.recursion (fun (m: nat) => m)
                        (fun (pred: nat) (rec: nat -> nat) (m: nat) => S (rec m)))
         (fun (pred: nat) (rec: nat -> nat -> nat) =>
            (fun a b => Nat.recursion 1 (fun pred1 rec1 => rec a rec1) b))
         pred0)
    n.

Lemma iter_proper: forall f1 f2,
    (forall x, f1 x = f2 x) ->
    forall b, iter f1 b = iter f2 b.
Proof.
  induction b.
  - reflexivity.
  - simpl. rewrite IHb. apply H.
Qed.

Definition iter' (f : nat -> nat) : nat -> nat :=
  Nat.recursion 1 (fun (pred: nat) (rec: nat) => f rec).

Lemma iter'_equiv: forall f b, iter' f b = iter f b.
Proof. induction b; intros; simpl; congruence. Qed.

Definition add': nat -> nat -> nat :=
  Nat.recursion (fun (m: nat) => m) (fun (pred: nat) (rec: nat -> nat) (m: nat) => S (rec m)).

Lemma add'_equiv: forall n m, add' n m = Nat.add n m.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite <- IHn. reflexivity.
Qed.

Definition mul': nat -> nat -> nat :=
  Nat.recursion (fun (m: nat) => 0)
                (fun (pred: nat) (rec: nat -> nat) (m: nat) => add' m (rec m)).

Lemma mul'_equiv: forall n m, mul' n m = Nat.mul n m.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite <- IHn. rewrite add'_equiv. reflexivity.
Qed.

Definition pow'(n: nat): nat -> nat :=
  Nat.recursion 1 (fun (pred: nat) (rec: nat) => mul' n rec).

Lemma pow'_equiv: forall n m, pow' n m = Nat.pow n m.
Proof.
  induction m; intros; simpl.
  - reflexivity.
  - rewrite <- IHm. rewrite mul'_equiv. reflexivity.
Qed.

Lemma ack'_equiv: forall n a b, ack' n a b = ack n a b.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - destruct n.
    + simpl. apply add'_equiv.
    + specialize (IHn a).
      rewrite <- (iter_proper _ _ IHn).
      rewrite <- iter'_equiv. reflexivity.
Qed.

Lemma ack'_reification_helper: exists res,
    interp_term nil res
    = existT _ (tpArr tpNat (tpArr tpNat (tpArr tpNat tpNat))) ack'.
Proof.
  eexists.
  unfold ack'.
  repeat t.
  all: reflexivity.
Defined.

Definition ack_reified: term.
  let r := eval unfold ack'_reification_helper in ack'_reification_helper in
  match r with
  | ex_intro _ ?x _ => exact x
  end.
Defined.

Lemma interp_ack_reified: projT2 (interp_term nil ack_reified) = ack'.
Proof. reflexivity. Qed.

Eval cbv in (term_depth ack_reified).

Definition contender_4': nat.
  let r := eval unfold pow', mul', add' in (ack' 5 (mul' 6 7) (S (S (pow' 10 4)))) in exact r.
Defined.

Lemma f_equal_ack'_equiv: forall n a b1 b2 : nat,
    b1 = b2 ->
    ack' n a b1 = ack n a b2.
Proof.
  intros.
  rewrite ack'_equiv.
  f_equal.
  assumption.
Qed.

Lemma contender_4'_equiv: contender_4' = contender_4.
Proof.
  unfold contender_4', contender_4.
  apply f_equal_ack'_equiv.
  vm_compute.
  reflexivity.
Qed.

Definition contender_4'': nat.
  let r := eval unfold contender_4', ack' in contender_4' in exact r.
Defined.

Lemma contender_4''_equiv: contender_4'' = contender_4.
Proof.
  etransitivity. 2: exact contender_4'_equiv.
  unfold contender_4'', contender_4'.
  unfold ack'.
  repeat apply f_equal.
  reflexivity.
Qed.

Lemma contender_4''_reification_helper: exists res,
    interp_term nil res
    = existT _ tpNat contender_4''.
Proof.
  eexists.
  unfold contender_4''.
  repeat t.
  all: reflexivity.
Defined.

Definition contender_4''_reified: term.
  let r := eval unfold contender_4''_reification_helper in contender_4''_reification_helper in
  match r with
  | ex_intro _ ?x _ => exact x
  end.
Defined.

Lemma interp_contender_4''_reified:
  projT2 (interp_term nil contender_4''_reified) = contender_4''.
Proof.
  cbv -[Nat.recursion].
  repeat apply f_equal.
  reflexivity.
Qed.

Lemma eval_contender_4''_reified:
  eval contender_4''_reified = contender_4''.
Proof.
  unfold eval.
  cbv -[Nat.recursion].
  repeat apply f_equal.
  reflexivity.
Qed.

Eval cbv in (term_depth contender_4''_reified).


(* Proving that the new contender is bigger than the previous one: *)

Lemma maxBy_In{T: Type}: forall f (l: list T) currentMax currentBest,
    currentMax = f currentBest ->
    List.In (maxBy f currentMax currentBest l) l \/ maxBy f currentMax currentBest l = currentBest.
Proof.
  induction l; intros.
  - simpl. auto.
  - subst. simpl in *.
    destruct (f currentBest <? f a) eqn: E.
    + specialize (IHl (f a) _ eq_refl). firstorder congruence.
    + specialize (IHl (f currentBest) _ eq_refl). firstorder congruence.
Qed.

Lemma maxBy_at_least_currentMax{T: Type}: forall (f: T -> nat) l currentMax currentBest,
    f currentBest = currentMax ->
    currentMax <= f (maxBy f currentMax currentBest l).
Proof.
  induction l; intros; simpl in *.
  - lia.
  - subst. destruct (f currentBest <? f a) eqn: E.
    + apply Nat.ltb_lt in E.
      specialize (IHl (f a) _ eq_refl).
      lia.
    + apply Nat.ltb_ge in E.
      eapply IHl.
      reflexivity.
Qed.

Lemma lowerbound_maxBy{T: Type}: forall (f: T -> nat) x l currentMax currentBest,
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
        eapply maxBy_at_least_currentMax.
        reflexivity.
      * apply Nat.ltb_ge in E.
        eapply Nat.le_trans. 1: eassumption.
        eapply maxBy_at_least_currentMax.
        reflexivity.
    + subst.
      destruct (f currentBest <? f a) eqn: E.
      * apply Nat.ltb_lt in E.
        eauto.
      * apply Nat.ltb_ge in E.
        eauto.
Qed.

Lemma upperbound_eval: forall t,
    eval t <= eval (largest_of_depth (term_depth t)).
Proof.
  intros. unfold largest_of_depth.
  eapply Nat.le_trans. 2: {
    eapply lowerbound_maxBy with (x := t). 2: reflexivity.
    eapply termsUpTo_correct.
    lia.
  }
  lia.
Qed.

Lemma maxBy_monotone{T: Type}: forall f (l1 l2: list T) currentMax currentBest,
    (forall x, In x l1 -> In x l2) ->
    f currentBest = currentMax ->
    f (maxBy f currentMax currentBest l1) <= f (maxBy f currentMax currentBest l2).
Proof.
  intros. subst.
  pose proof (maxBy_In f l1 (f currentBest) _ eq_refl) as P.
  destruct P as [P | P].
  - specialize (H _ P).
    eapply lowerbound_maxBy. 1: exact H. reflexivity.
  - rewrite P. eapply maxBy_at_least_currentMax. reflexivity.
Qed.

Lemma largest_of_depth_monotone: forall n1 n2,
    n1 <= n2 ->
    eval (largest_of_depth n1) <= eval (largest_of_depth n2).
Proof.
  intros.
  unfold largest_of_depth.
  eapply (maxBy_monotone eval (termsUpTo n1) (termsUpTo n2)). 2: reflexivity.
  intros.
  eapply termsUpTo_correct.
  eapply termsUpTo_correct in H0.
  eapply Nat.le_trans; eassumption.
Qed.

Lemma largest_of_depth_strictly_monotone: forall n1 n2,
    0 < n1 < n2 ->
    eval (largest_of_depth n1) < eval (largest_of_depth n2).
Proof.
  intros.
  unfold largest_of_depth.
  destruct n2 as [|n2]. 1: exfalso; lia.
  simpl.
  eapply Nat.le_lt_trans. 1: eapply largest_of_depth_monotone with (n2 := n2). 1: lia.
  unfold largest_of_depth.
  eapply Nat.lt_le_trans. 2: {
    eapply lowerbound_maxBy with (x := (tApp tS (maxBy eval 0 tO (termsUpTo n2)))).
    2: reflexivity.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; left.
    match goal with
    | |- In (tApp ?t1 ?t2) (map _ _) =>
      change (tApp t1 t2) with ((fun '(t10, t20) => tApp t10 t20) (t1, t2))
    end.
    eapply in_map.
    apply in_prod.
    - destruct n2 as [|n2]. 1: exfalso; lia.
      simpl.
      do 3 (apply in_app_iff; right).
      simpl. auto.
    - pose proof (maxBy_In eval (termsUpTo n2) 0 tO eq_refl) as P.
      destruct P as [P | P].
      + exact P.
      + rewrite P.
        destruct n2 as [|n2]. 1: exfalso; lia.
        simpl.
        do 3 (apply in_app_iff; right).
        simpl. auto.
  }
  generalize (maxBy eval 0 tO (termsUpTo n2)). intro t.
  unfold eval.
  simpl.
  destruct (interp_term [] t) as [tp1 r1] eqn: E1.
  destruct tp1 as [|A1 B1].
  - unfold cast, cast_impl. simpl. unfold id. lia.
  - lia.
Qed.

Theorem contender_4_lt_contender_5 : contender_4 < contender_5.
Proof.
  rewrite <- contender_4''_equiv.
  rewrite <- eval_contender_4''_reified.
  unfold contender_5, largest_STLCNatRec_nat_of_depth.
  eapply Nat.le_lt_trans.
  - eapply upperbound_eval.
  - eapply largest_of_depth_strictly_monotone.
    cbv.
    lia.
Qed.

Print Assumptions contender_4_lt_contender_5.


(* ===================================================================== *)
(* contender_6                                                           *)
(*                                                                       *)
(* Strategy: run the SAME depth-bounded-maximum construction that        *)
(* defines contender_5, but inside a strictly larger object language.    *)
(*                                                                       *)
(*   L_Grow :=  STLC+NatRec extended with one fresh primitive constant   *)
(*              [tGrow : Nat -> Nat], interpreted as                     *)
(*                                                                       *)
(*      BigGrow := f_epsilon_0     (the fast-growing hierarchy, indexed  *)
(*                                  at the proof-theoretic ordinal of PA)*)
(*                                                                       *)
(*   contender_6 :=  the largest nat any closed L_Grow term of depth     *)
(*                   at most 44 evaluates to.                            *)
(*                                                                       *)
(* The definition mentions none of contender_5's search machinery.  The  *)
(* proof of [contender_5 < contender_6] obtains -- existentially -- a    *)
(* maximizer term t_star of the depth-42 search behind contender_5,      *)
(* embeds it into L_Grow, and offers the depth-(at most)-44 term         *)
(*                                                                       *)
(*     tGrow (tS (embed t_star))                                         *)
(*                                                                       *)
(* as a witness to the new maximum, giving the explicit lower bound      *)
(*                                                                       *)
(*     BigGrow (S contender_5) <= contender_6.                           *)
(*                                                                       *)
(* That the embedding preserves evaluation is proved with a Tait-style   *)
(* logical relation, so no axioms (in particular no function             *)
(* extensionality) are needed anywhere.                                  *)
(*                                                                       *)
(* Submitted by V. Reshetnikov.                                          *)
(* ===================================================================== *)


(* --------------------------------------------------------------------- *)
(* Brouwer ordinal notations and the fast-growing hierarchy.              *)
(*                                                                        *)
(* A [Brouwer] tree is an ordinal notation in which every limit ordinal   *)
(* carries its own fundamental sequence: [Blim f] denotes sup_n f(n).     *)
(* Because the sequence is part of the data, every recursion below is     *)
(* structural -- no accessibility predicates, no fuel.                    *)
(* --------------------------------------------------------------------- *)

Inductive Brouwer : Type :=
| Bz    : Brouwer
| Bsucc : Brouwer -> Brouwer
| Blim  : (nat -> Brouwer) -> Brouwer.

Fixpoint Badd (a b : Brouwer) : Brouwer :=
  match b with
  | Bz       => a
  | Bsucc b' => Bsucc (Badd a b')
  | Blim f   => Blim (fun n => Badd a (f n))
  end.

(* a * n  =  a + a + ... + a  (n copies): all the multiplication that
   omega_pow needs. *)
Fixpoint BmulN (a : Brouwer) (n : nat) : Brouwer :=
  match n with
  | 0   => Bz
  | S m => Badd (BmulN a m) a
  end.

(* omega^a, by structural recursion on [a]:  omega^0 = 1, limits are
   taken pointwise, and omega^(a+1) = omega^a * omega is the limit of
   its own fundamental sequence  omega^a * n. *)
Fixpoint omega_pow (a : Brouwer) : Brouwer :=
  match a with
  | Bz       => Bsucc Bz
  | Bsucc a' => Blim (BmulN (omega_pow a'))
  | Blim f   => Blim (fun n => omega_pow (f n))
  end.

(* omega ^^ n: a tower of omegas of height n. *)
Fixpoint omega_tower (n : nat) : Brouwer :=
  match n with
  | 0    => Bsucc Bz
  | S n' => omega_pow (omega_tower n')
  end.

(* epsilon_0 = sup_n (omega ^^ n), the proof-theoretic ordinal of PA. *)
Definition epsilon_0 : Brouwer := Blim omega_tower.

(* The fast-growing hierarchy:
     f_0(n)     = n + 1,
     f_{a+1}(n) = f_a iterated n times starting from n,
     f_lam(n)   = f_{lam[n]}(n)   (via the [Blim] fundamental sequence). *)
Fixpoint FGH (a : Brouwer) (n : nat) : nat :=
  match a with
  | Bz       => S n
  | Bsucc a' => Nat.iter n (FGH a') n
  | Blim f   => FGH (f n) n
  end.

(* Every function in the hierarchy is inflationary. *)
Lemma FGH_ge : forall a n, n <= FGH a n.
Proof.
  induction a as [|a IHa|f IHf]; intro n; cbn; [lia| |apply IHf].
  enough (forall k x, x <= Nat.iter k (FGH a) x) by auto.
  intro k; induction k as [|k IHk]; intro x; cbn;
    [lia | etransitivity; [apply IHk | apply IHa]].
Qed.

Definition BigGrow (n : nat) : nat := FGH epsilon_0 n.

(* The one growth fact the whole proof needs. *)
Lemma BigGrow_gt_S : forall n, n < BigGrow (S n).
Proof.
  intro n. apply Nat.lt_le_trans with (S n); [lia | apply FGH_ge].
Qed.


(* --------------------------------------------------------------------- *)
(* From here on, contender_5's search machinery must never be unfolded    *)
(* by conversion: at depth 42 that would be a computation of astronomical *)
(* size.  We only ever reason about these constants through their lemmas, *)
(* restoring transparency locally in the few places that need to peek     *)
(* one definition deep.                                                   *)
(* --------------------------------------------------------------------- *)

Opaque eval maxBy termsUpTo typesUpTo natsUpTo
       largest_of_depth largest_STLCNatRec_nat_of_depth.


(* Step (A) of the proof: the maximum defining contender_5 is attained    *)
(* by some closed term of depth at most 42.  By [maxBy_In], the result of *)
(* [maxBy] is either an element of the searched list (depth <= 42 by      *)
(* [termsUpTo_correct]) or the initial best [tO] (depth 1).  Note that    *)
(* this is bare existence: nobody can compute t_star in this universe,    *)
(* but we only ever use the existential witness inside a proof.           *)

Local Transparent eval largest_of_depth largest_STLCNatRec_nat_of_depth.

Lemma exists_maximizer_42 :
  exists tstar : term,
    term_depth tstar <= 42 /\ eval tstar = contender_5.
Proof.
  unfold contender_5, largest_STLCNatRec_nat_of_depth, largest_of_depth.
  exists (maxBy eval 0 tO (termsUpTo 42)); split; [|reflexivity].
  destruct (maxBy_In eval (termsUpTo 42) 0 tO eq_refl) as [Pin | Peq].
  - apply (proj2 (termsUpTo_correct 42 _)) in Pin. exact Pin.
  - rewrite Peq. simpl. lia.
Qed.

Local Opaque eval largest_of_depth largest_STLCNatRec_nat_of_depth.


(* --------------------------------------------------------------------- *)
(* The new object language L_Grow.                                        *)
(*                                                                        *)
(* Everything in this module is a line-for-line copy of the STLC+NatRec   *)
(* development above, plus exactly one new constant [tGrow] (of depth 1,  *)
(* like [tO] and [tS]), interpreted as [BigGrow].  Types and their        *)
(* interpretation are shared with the old language; only terms are new.   *)
(* --------------------------------------------------------------------- *)

Module LGrow.

Definition pack := {tp : type & interp_type tp}.

Inductive term :=
| tVar (x : nat)
| tLam (A B : type) (body : term)
| tApp (t1 t2 : term)
| tO
| tS
| tNatRec (R : type)
| tGrow.

Fixpoint term_depth (t : term) : nat :=
  match t with
  | tVar x => S (nat_depth x)
  | tLam A B body =>
      S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
  | tGrow => 1
  end.

Fixpoint interp_term (e : list pack) (t : term) : pack :=
  match t with
  | tVar x =>
      match lookup e x with
      | Some R => R
      | None   => existT _ tpNat error
      end
  | tLam A B body =>
      existT _ (tpArr A B)
             (fun x' => cast B (projT2 (interp_term ((existT _ A x') :: e) body)))
  | tApp t1 t2 =>
      let '(existT _ R1 r1) := interp_term e t1 in
      let '(existT _ R2 r2) := interp_term e t2 in
      match R1 as R1' return interp_type R1' -> pack with
      | tpNat       => fun _  => existT _ tpNat error
      | tpArr A B   => fun r1 => existT _ B (r1 (cast A r2))
      end r1
  | tO       => existT _ tpNat 0
  | tS       => existT _ (tpArr tpNat tpNat) S
  | tNatRec R =>
      existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R)))
             (@Nat.recursion (interp_type R))
  | tGrow    => existT _ (tpArr tpNat tpNat) BigGrow
  end.

Definition eval (t : term) : nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat => fun res : interp_type tpNat => res
  | tpArr _ _ => fun _ => 0
  end res.

(* The depth-bounded enumerator: same segments as the old [termsUpTo]    *)
(* (reordered, atoms first), plus [tGrow] among the atoms.               *)
Fixpoint termsUpTo (n : nat) : list term :=
  match n with
  | O => []
  | S m =>
    tO :: tS :: tGrow ::
    List.map tVar (natsUpTo m) ++
    List.map tNatRec (typesUpTo m) ++
    List.map (fun '(A, B, body) => tLam A B body)
             (list_prod (list_prod (typesUpTo m) (typesUpTo m)) (termsUpTo m)) ++
    List.map (fun '(t1, t2) => tApp t1 t2)
             (list_prod (termsUpTo m) (termsUpTo m))
  end.

(* Only completeness is needed: every term of depth <= n is enumerated. *)
Lemma termsUpTo_complete : forall n t,
    term_depth t <= n -> List.In t (termsUpTo n).
Proof.
  induction n; intros t H; [destruct t; simpl in H; lia|].
  destruct t as [x|A B body|t1 t2| | |R|]; simpl in H; simpl; auto;
    do 3 right; rewrite !in_app_iff.
  - left. apply in_map, natsUpTo_correct. lia.
  - do 2 right; left.
    match goal with |- In ?e (map ?f _) => change e with (f (A, B, body)) end.
    apply in_map.
    apply in_prod; [apply in_prod; apply typesUpTo_correct | apply IHn]; lia.
  - do 3 right.
    match goal with |- In ?e (map ?f _) => change e with (f (t1, t2)) end.
    apply in_map. apply in_prod; apply IHn; lia.
  - right; left. apply in_map, typesUpTo_correct. lia.
Qed.

Definition largest_of_depth (n : nat) : term :=
  maxBy eval 0 tO (termsUpTo n).

Definition largest_LGrow_nat_of_depth (n : nat) : nat :=
  eval (largest_of_depth n).

(* -------------------------------------------------------------------- *)
(* The embedding of the old language into L_Grow, and step (B) of the    *)
(* proof: the embedding preserves evaluation.                            *)
(* -------------------------------------------------------------------- *)

Fixpoint embed_term (t : Contender.term) : term :=
  match t with
  | Contender.tVar x => tVar x
  | Contender.tLam A B body => tLam A B (embed_term body)
  | Contender.tApp t1 t2 => tApp (embed_term t1) (embed_term t2)
  | Contender.tO => tO
  | Contender.tS => tS
  | Contender.tNatRec R => tNatRec R
  end.

Lemma term_depth_embed : forall t,
    term_depth (embed_term t) = Contender.term_depth t.
Proof. induction t; simpl; congruence. Qed.

(* Naive equality of the two interpretations fails at arrow types
   without function extensionality, so we use a Tait-style logical
   relation instead.  It collapses to plain equality at [tpNat] --
   which is all [eval] looks at.                                       *)
Fixpoint RelVal (A : type) : interp_type A -> interp_type A -> Prop :=
  match A with
  | tpNat => fun x y => x = y
  | tpArr A1 A2 => fun f g => forall x y, RelVal A1 x y -> RelVal A2 (f x) (g y)
  end.

(* Two packs are related when they carry the SAME type tag and related
   values at that tag.  (Stated with explicit equations rather than as
   an inductive, so that destructing it never needs axiom K.)           *)
Definition RelPack (p q : pack) : Prop :=
  exists tp (v1 v2 : interp_type tp),
    p = existT interp_type tp v1
    /\ q = existT interp_type tp v2
    /\ RelVal tp v1 v2.

Lemma RelPack_intro :
  forall tp (v1 v2 : interp_type tp),
    RelVal tp v1 v2 ->
    RelPack (existT interp_type tp v1) (existT interp_type tp v2).
Proof. intros tp v1 v2 H; exists tp, v1, v2; repeat split; assumption. Qed.

Lemma error_related : forall tp, RelVal tp (@error tp) (@error tp).
Proof. induction tp; simpl; [reflexivity | intros _ _ _; exact IHtp2]. Qed.

(* A related environment is ONE list whose entries each carry a type
   tag, a value for either side, and the proof that the two values are
   related.  Projecting out the first / second components gives the two
   environments the fundamental lemma talks about; bundling the proofs
   into the entries makes a pointwise list relation (and the length
   bookkeeping it would drag in) unnecessary.                           *)
Record REntry := mkREntry {
  rtp  : type;
  rv1  : interp_type rtp;
  rv2  : interp_type rtp;
  rrel : RelVal rtp rv1 rv2
}.

Definition rfst (r : REntry) : pack := existT interp_type (rtp r) (rv1 r).
Definition rsnd (r : REntry) : pack := existT interp_type (rtp r) (rv2 r).

(* The two projected environments have equal lengths by construction,
   so the reverse-indexed [lookup] either misses on both sides or finds
   the two halves of the same entry.                                    *)
Lemma lookup_related :
  forall (e : list REntry) n,
    match lookup (map rfst e) n, lookup (map rsnd e) n with
    | Some p1, Some p2 => RelPack p1 p2
    | None, None => True
    | _, _ => False
    end.
Proof.
  intros e n. unfold lookup. cbv zeta. rewrite !length_map.
  destruct (length e <=? n); [exact I|].
  rewrite !nth_error_map.
  destruct (nth_error e (length e - S n)) as [[tp v1 v2 Hrel]|]; cbn;
    [apply RelPack_intro; exact Hrel | exact I].
Qed.

Local Opaque lookup.

(* [cast_impl from to] preserves the relation, in both directions at
   once -- the two directions are interlocked because casting a
   function casts its argument *backward*. *)
Lemma cast_impl_related : forall from to,
    (forall v1 v2,
        RelVal from v1 v2 ->
        RelVal to (fst (cast_impl from to) v1)
                  (fst (cast_impl from to) v2))
    /\
    (forall u1 u2,
        RelVal to u1 u2 ->
        RelVal from (snd (cast_impl from to) u1)
                    (snd (cast_impl from to) u2)).
Proof.
  induction from as [|from1 IH1 from2 IH2]; intros [|to1 to2]; simpl;
    try (split; intros; assumption);
    try (split; intros _ _ _; simpl;
         (reflexivity || (intros; apply error_related))).
  destruct (type_eqb from1 to1) eqn:E1;
  destruct (type_eqb from2 to2) eqn:E2; simpl;
    try (split; intros _ _ _; simpl; intros; apply error_related).
  destruct (IH1 to1) as [IH1fw IH1bw], (IH2 to2) as [IH2fw IH2bw].
  destruct (cast_impl from1 to1) eqn:C1.
  destruct (cast_impl from2 to2) eqn:C2.
  split; intros f g Hfg x y Hxy; simpl in *.
  - apply IH2fw. apply Hfg. apply IH1bw. exact Hxy.
  - apply IH2bw. apply Hfg. apply IH1fw. exact Hxy.
Qed.

Lemma cast_related : forall from to v1 v2,
    RelVal from v1 v2 ->
    RelVal to (@cast from to v1) (@cast from to v2).
Proof. intros; apply (proj1 (cast_impl_related _ _)); assumption. Qed.

(* The fundamental theorem of the embedding: under the two projections
   of a related environment, a term and its embedding interpret to
   related packs. *)
Lemma embed_interp_related :
  forall (e : list REntry) t,
    RelPack (Contender.interp_term (map rfst e) t)
            (interp_term (map rsnd e) (embed_term t)).
Proof.
  intros e t. revert e.
  induction t as [x|A B body IH|t1 IH1 t2 IH2| | |R]; intro e.
  - (* tVar.  Make both sides explicit [match lookup] expressions, then
       [lookup_related] rules out the one-sided cases. *)
    change
      (RelPack
         (match lookup (map rfst e) x with
          | Some p => p
          | None => existT interp_type tpNat (@error tpNat)
          end)
         (match lookup (map rsnd e) x with
          | Some p => p
          | None => existT interp_type tpNat (@error tpNat)
          end)).
    pose proof (lookup_related e x) as Hlk.
    destruct (lookup (map rfst e) x), (lookup (map rsnd e) x);
      simpl in Hlk; try contradiction.
    + exact Hlk.
    + apply RelPack_intro; reflexivity.
  - (* tLam.  Both sides are explicit packs at tag [tpArr A B]; the IH,
       at the environment extended with the entry (A, x, y, Hxy),
       relates the bodies, and [cast_related] pushes that through the
       final cast. *)
    change
      (RelPack
         (existT interp_type (tpArr A B)
            (fun x' : interp_type A =>
               cast B (projT2 (Contender.interp_term
                                 (existT _ A x' :: map rfst e) body))))
         (existT interp_type (tpArr A B)
            (fun x' : interp_type A =>
               cast B (projT2 (interp_term
                                 (existT _ A x' :: map rsnd e)
                                 (embed_term body)))))).
    apply RelPack_intro. simpl. intros x y Hxy.
    assert (RelPack
              (Contender.interp_term (existT _ A x :: map rfst e) body)
              (interp_term (existT _ A y :: map rsnd e) (embed_term body)))
      as (tpb & rb1 & rb2 & -> & -> & Hrb)
      by exact (IH (mkREntry A x y Hxy :: e)).
    simpl. apply cast_related, Hrb.
  - (* tApp.  Both sides match on the function's type tag; the [tpArr]
       branch follows from the IHs and [cast_related], the [tpNat]
       branch falls to [error] on both sides. *)
    cbn [Contender.interp_term interp_term embed_term].
    destruct (IH1 e) as (tp1 & v1 & v1' & -> & -> & Hrel1).
    destruct (IH2 e) as (tp2 & v2 & v2' & -> & -> & Hrel2).
    simpl; destruct tp1 as [|A B]; [apply RelPack_intro; reflexivity|].
    apply RelPack_intro; apply Hrel1, cast_related, Hrel2.
  - (* tO *)
    apply RelPack_intro. reflexivity.
  - (* tS *)
    apply RelPack_intro; simpl; intros x y Hxy; subst; reflexivity.
  - (* tNatRec.  [Nat.recursion] respects the relation: equal counters
       plus related base/step values give related results. *)
    apply RelPack_intro. simpl.
    intros base1 base2 Hbase step1 step2 Hstep n1 n2 Hn. subst n2.
    revert base1 base2 Hbase step1 step2 Hstep.
    induction n1; intros; simpl;
      [exact Hbase | apply Hstep; [reflexivity | apply IHn1; assumption]].
Qed.

(* Specialized to closed terms, the relation IS equality of the two
   evaluators, because [RelVal tpNat] is equality and both evaluators
   return 0 at arrow tags.  ([Contender.eval] must be unfolded once,
   so transparency is restored just for this proof.) *)
Local Transparent Contender.eval.

Lemma embed_eval : forall t,
    eval (embed_term t) = Contender.eval t.
Proof.
  intro t.
  pose proof (embed_interp_related [] t)
    as (tp & v1 & v2 & Hp1 & Hp2 & Hrel).
  unfold eval, Contender.eval.
  replace (Contender.interp_term nil t) with (existT interp_type tp v1)
    by (symmetry; exact Hp1).
  replace (interp_term nil (embed_term t)) with (existT interp_type tp v2)
    by (symmetry; exact Hp2).
  destruct tp; [symmetry; exact Hrel | reflexivity].
Qed.

Local Opaque Contender.eval.

(* -------------------------------------------------------------------- *)
(* Step (C): the witness term and its two properties.                    *)
(* -------------------------------------------------------------------- *)

Definition witness (t : Contender.term) : term :=
  tApp tGrow (tApp tS (embed_term t)).

Lemma witness_depth : forall t,
    Contender.term_depth t <= 42 ->
    term_depth (witness t) <= 44.
Proof.
  intros t H. unfold witness. cbn [term_depth].
  rewrite term_depth_embed. lia.
Qed.

(* Evaluating the witness applies [BigGrow] after [S] -- with no side
   condition on [t]: if [embed_term t] happens to have an arrow type,
   both sides collapse to [BigGrow 1] because [S] casts its argument
   to [error = 0] and [eval t] is 0 as well.                            *)
Lemma witness_eval : forall t,
    eval (witness t) = BigGrow (S (Contender.eval t)).
Proof.
  intro t. rewrite <- (embed_eval t). unfold witness, eval.
  destruct (interp_term [] (embed_term t)) as [[|A B] v] eqn:E;
    cbn [interp_term]; rewrite E; reflexivity.
Qed.

End LGrow.

(* The new contender: the largest value reached by any closed L_Grow    *)
(* term of depth at most 44.  Its unfolding mentions only L_Grow's own  *)
(* evaluator and enumerator plus the generic [maxBy] -- no contender_5  *)
(* machinery.                                                           *)
Definition contender_6 : nat := LGrow.largest_LGrow_nat_of_depth 44.

(* The explicit lower bound: chain (A), (B), (C) through the generic    *)
(* [lowerbound_maxBy].                                                  *)
Theorem BigGrow_lower_bound : BigGrow (S contender_5) <= contender_6.
Proof.
  unfold contender_6, LGrow.largest_LGrow_nat_of_depth,
         LGrow.largest_of_depth.
  destruct exists_maximizer_42 as (tstar & Hdepth & Heval).
  rewrite <- Heval, <- LGrow.witness_eval.
  apply lowerbound_maxBy.
  - apply LGrow.termsUpTo_complete, LGrow.witness_depth, Hdepth.
  - reflexivity.
Qed.

Theorem contender_5_lt_contender_6 : contender_5 < contender_6.
Proof.
  apply Nat.lt_le_trans with (m := BigGrow (S contender_5)).
  - apply BigGrow_gt_S.
  - exact BigGrow_lower_bound.
Qed.

Print Assumptions BigGrow_lower_bound.
Print Assumptions contender_5_lt_contender_6.

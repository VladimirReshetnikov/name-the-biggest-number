(* Sandbox: second-order reflection (Approach D.2 from IDEAS.md).

   We build a new object language:

     STLC + NatRec + a primitive
       tRTower : Nat -> Nat -> Nat

   interpreted as the *already-constructed* reflection tower from
   [sandbox/ReflectTower.v]:

     sandbox.ReflectTower.ReflectTower.R_tower : nat -> nat -> nat.

   Then we define a new depth-bounded maximum over this extended language:

     largest_RT_nat_of_depth d := max value of eval over termsUpTo d

   and show it beats contender_5 by exhibiting a witness term

     S (tRTower K D)

   In this sandbox we use unary literals for K and D (the mechanically
   simplest proof).  The interesting next refinement is to compute large K/D
   values at small [term_depth] and feed them to RTower; doing that cleanly
   needs care because this syntax uses de Bruijn *levels* (see [lookup]), so
   reusable arithmetic combinators require shifting.

   Compile from repo root (after Contender.vo exists):

     coqc -Q . "" sandbox\ReflectRTower.v
*)

Require Import Arith Lia.
Require Import List. Import ListNotations.

Require Contender.
Require Import sandbox.ReflectTower.

(* Keep the huge enumerations opaque in any conversion checks we trigger. *)
Opaque Contender.largest_STLCNatRec_nat_of_depth.

(* The oracle we reflect: the stratified reflection tower from ReflectTower.v. *)
Definition RTower : nat -> nat -> nat := sandbox.ReflectTower.ReflectTower.R_tower.
Opaque sandbox.ReflectTower.ReflectTower.R_tower.

Lemma contender_reflect_tower_7_eq_RTower_100_342 :
  sandbox.ReflectTower.ReflectTower.contender_reflect_tower_7 = RTower 100 342.
Proof.
  unfold sandbox.ReflectTower.ReflectTower.contender_reflect_tower_7, RTower.
  reflexivity.
Qed.

Lemma contender_5_lt_RTower_100_342 :
  Contender.contender_5 < RTower 100 342.
Proof.
  pose proof sandbox.ReflectTower.ReflectTower.contender_5_lt_reflect_tower_7 as H.
  rewrite contender_reflect_tower_7_eq_RTower_100_342 in H.
  exact H.
Qed.

(* -------------------------------------------------------------------- *)
(* Pure syntax: types, terms, depths.                                    *)
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

Fixpoint interp_term (rt : nat -> nat -> nat) (e : list {tp : type & interp_type tp})
         (t : term) : {tp : type & interp_type tp} :=
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
(* Depth-bounded enumeration.                                            *)
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
  - assert (n = m \/ S m <= n) as C by lia. destruct C as [C | C]; firstorder idtac.
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

(* From this point on, keep the enumerator opaque: any conversion that tries
   to unfold [termsUpTo 345] (or similar) will immediately explode. *)
Opaque termsUpTo.

(* -------------------------------------------------------------------- *)
(* Max-by and the depth-bounded maximum.                                 *)
(* -------------------------------------------------------------------- *)

Fixpoint maxBy {T : Type} (f : T -> nat) (currentMax : nat) (currentBest : T) (l : list T) : T :=
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
(* Small-depth arithmetic terms for K and D.                              *)
(* -------------------------------------------------------------------- *)

Fixpoint natlit (n : nat) : term :=
  match n with
  | O => tO
  | S n' => tApp tS (natlit n')
  end.

(* For the mechanical proof below we keep K and D as unary literals.

   Note: this is *not* inherent.  D.2 is the first point where it becomes
   attractive to compute large K/D inside the object language (so their
   [term_depth] stays small) while still feeding huge numeric inputs to RTower.
   Getting that right needs care because this term language uses de Bruijn
   *levels* (see [lookup]), so reusable combinator terms require shifting.
*)

Definition t100 : term := natlit 100.
Definition t342 : term := natlit 342.

Definition witness_rtower : term :=
  tApp tS (tApp (tApp tRTower t100) t342).

Lemma eval_witness_rtower :
  eval RTower witness_rtower = S (RTower 100 342).
Proof.
  (* Avoid [vm_compute] here: if RTower is ever treated as transparent, the VM
     will eagerly try to reduce [RTower 100 342], i.e. a depth-342 reflective
     maximum, which is exactly the explosion we want to stay symbolic about. *)
  unfold witness_rtower, eval.
  cbn.
  reflexivity.
Qed.

Lemma eval_tO : forall rt, eval rt tO = 0.
Proof. intro rt. reflexivity. Qed.

(* The depth budget for this unary-literal D.2 witness is 345. *)
Definition depth_rtower_8 : nat := term_depth witness_rtower.

Eval vm_compute in depth_rtower_8.

(* From here on, keep the evaluator / maxBy opaque: otherwise Coq's conversion
   checks may try to reduce [eval RTower (maxBy ... (termsUpTo 345))], which
   would amount to actually running the depth-bounded search. *)
Opaque eval.
Opaque maxBy.

Definition contender_reflect_rtower_8 : nat :=
  largest_RT_nat_of_depth RTower depth_rtower_8.

Lemma contender_reflect_rtower_8_at_least :
  S (RTower 100 342) <= contender_reflect_rtower_8.
Proof.
  unfold contender_reflect_rtower_8, largest_RT_nat_of_depth, largest_of_depth.
  rewrite <- eval_witness_rtower.
  eapply lowerbound_maxBy with (x := witness_rtower).
  - apply termsUpTo_correct. unfold depth_rtower_8. lia.
  - apply eval_tO.
Qed.

Theorem contender_5_lt_reflect_rtower_8 :
  Contender.contender_5 < contender_reflect_rtower_8.
Proof.
  eapply Nat.lt_le_trans with (m := S (RTower 100 342)).
  - eapply Nat.lt_trans.
    + exact contender_5_lt_RTower_100_342.
    + apply Nat.lt_succ_diag_r.
  - exact contender_reflect_rtower_8_at_least.
Qed.

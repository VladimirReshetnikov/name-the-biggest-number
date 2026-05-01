(* Sandbox: Approach M -- embedding-witness fresh-engine shell.  (WIP)

   This file implements the "clean-definition, proof-witness reuse" idea
   from IDEAS.md / reviews/review-{1,2,3}.md:

     - Define a fresh object language L_Grow = STLC+NatRec + tGrow,
       where tGrow : Nat -> Nat is interpreted as a total nat->nat
       growth engine (instantiated here with Brouwer.BigGrow).

     - The contender definition is the depth-bounded maximum in L_Grow:

         contender_grow_6 := largest_Grow_nat_of_depth 44

       It mentions no previous-max oracle machinery.

     - The proof extracts the previous maximizer term t* for contender_5
       (via maxBy_In), embeds it into L_Grow, and uses the witness term

         tGrow (S (embed t_star))

       at depth 44 to establish the explicit lower bound

         grow (S contender_5) <= contender_grow_6

       and hence the strict inequality contender_5 < contender_grow_6
       assuming grow_gt_S : forall n, n < grow (S n).

   Compile from repo root, after Contender.vo and sandbox/Brouwer.vo exist:

     coqc -Q . "" sandbox\GrowEmbed.v
*)

Require Import Arith Lia.
Require Import List. Import ListNotations.

Require Contender.
Require Import sandbox.Brouwer.

(* Coq kernel conversion must never try to unfold depth-bounded search at a
   concrete depth like 42.  Keep Contender's max/search machinery opaque in
   this file.  (We only use its lemmas about these constants.) *)
Opaque Contender.eval.
Opaque Contender.maxBy.
Opaque Contender.termsUpTo.
Opaque Contender.typesUpTo.
Opaque Contender.natsUpTo.
Opaque Contender.largest_of_depth.
Opaque Contender.largest_STLCNatRec_nat_of_depth.

Module Type GrowSig.
  Parameter grow : nat -> nat.
  Axiom grow_gt_S : forall n, n < grow (S n).
End GrowSig.

Module GrowEmbed (G : GrowSig).

(* -------------------------------------------------------------------- *)
(* Syntax: STLC+NatRec + a fresh unary growth primitive [tGrow].         *)
(* Types are shared with Contender's STLC+NatRec definitions.            *)
(* -------------------------------------------------------------------- *)

Definition type := Contender.type.
Definition interp_type := Contender.interp_type.

Notation tpNat := Contender.tpNat.
Notation tpArr := Contender.tpArr.

Definition pack := {tp : Contender.type & Contender.interp_type tp}.

Inductive term :=
| tVar (x : nat)
| tLam (A B : type) (body : term)
| tApp (t1 t2 : term)
| tO
| tS
| tNatRec (R : type)
| tGrow.

(* Depth accounting: re-use the exact measures from Contender's STLC+NatRec. *)

Definition nat_depth := Contender.nat_depth.
Definition type_depth := Contender.type_depth.

Fixpoint term_depth (t : term) : nat :=
  match t with
  | tVar x => S (nat_depth x)
  | tLam A B body => S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
  | tGrow => 1
  end.

Definition error {tp : type} : interp_type tp := Contender.error (tp := tp).
Definition cast {from : type} (to : type) : interp_type from -> interp_type to :=
  Contender.cast (from := from) to.

Definition interp_term :
  forall (e : list pack) (t : term),
    pack.
  refine (fix rec e t {struct t} :=
    match t with
    | tVar x => _
    | tLam A B body => _
    | tApp t1 t2 => _
    | tO => _
    | tS => _
    | tNatRec R => _
    | tGrow => _
    end).
  - destruct (Contender.lookup e x) as [R|].
    + exact R.
    + exact (existT _ tpNat error).
  - refine (existT _ (tpArr A B) _).
    intro x'.
    set (r := projT2 (rec (existT _ A x' :: e) body)).
    exact (cast B r).
  - destruct (rec e t1) as [R1 r1].
    destruct (rec e t2) as [R2 r2].
    destruct R1 as [|A B]; [exact (existT _ tpNat error)|].
    exact (existT _ B (r1 (cast A r2))).
  - exact (existT _ tpNat 0).
  - exact (existT _ (tpArr tpNat tpNat) S).
  - exact (existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R)))
                   (@Nat.recursion (interp_type R))).
  - exact (existT _ (tpArr tpNat tpNat) G.grow).
Defined.

Definition eval (t : term) : nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat => fun res : interp_type tpNat => res
  | tpArr _ _ => fun _ => 0
  end res.

(* Simple reduction lemmas for the witness chain (no FunExt needed). *)

Lemma cast_nat_id : forall (a : nat), @cast tpNat tpNat a = a.
Proof. intro a. reflexivity. Qed.

Lemma interp_tO : forall e, interp_term e tO = existT _ tpNat 0.
Proof. intros. reflexivity. Qed.

Lemma interp_tS : forall e, interp_term e tS = existT _ (tpArr tpNat tpNat) S.
Proof. intros. reflexivity. Qed.

Lemma interp_tGrow : forall e, interp_term e tGrow = existT _ (tpArr tpNat tpNat) G.grow.
Proof. intros. reflexivity. Qed.

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

(* -------------------------------------------------------------------- *)
(* Enumeration for L_Grow: copy Contender's depth-bounded generator and  *)
(* add the new constant [tGrow].                                        *)
(* -------------------------------------------------------------------- *)

Definition typesUpTo : nat -> list type := Contender.typesUpTo.

Lemma typesUpTo_correct : forall n t,
    type_depth t <= n <-> List.In t (typesUpTo n).
Proof. exact Contender.typesUpTo_correct. Qed.

Definition natsUpTo : nat -> list nat := Contender.natsUpTo.

Lemma natsUpTo_correct : forall n m,
    nat_depth m <= n <-> List.In m (natsUpTo n).
Proof. exact Contender.natsUpTo_correct. Qed.

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
    [tGrow]
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
    + do 3 (apply in_or_app; right).
      simpl.
      right. right.
      apply in_app_iff; left.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia].
    + do 3 (apply in_or_app; right).
      simpl.
      right. right.
      apply in_app_iff; right.
      simpl. auto.
  - simpl in *.
    repeat ((simpl in H || apply in_app_iff in H || idtac); destruct H).
    + apply in_map_iff in H.
      destruct H as [x [? H]]. subst t.
      pose proof ((proj2 (natsUpTo_correct _ _)) H).
      simpl. lia.
    + apply in_map_iff in H.
      destruct H as [[[A B] body] [? H]]. subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H1).
      pose proof ((proj2 (IHn _)) H0).
      simpl. lia.
    + apply in_map_iff in H.
      destruct H as [[t1 t2] [? H]]. subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (IHn _)) H).
      pose proof ((proj2 (IHn _)) H0).
      simpl. lia.
    + simpl. lia.
    + simpl. lia.
    + apply in_map_iff in H.
      destruct H as [R [? H]]. subst t.
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      simpl. lia.
    + simpl. lia.
Qed.

Fixpoint maxBy {T : Type} (f : T -> nat) (currentMax : nat) (currentBest : T) (l : list T) : T :=
  match l with
  | nil => currentBest
  | cons h t =>
      if currentMax <? (f h) then
        maxBy f (f h) h t
      else
        maxBy f currentMax currentBest t
  end.

Definition largest_of_depth (n : nat) : term :=
  maxBy eval 0 tO (termsUpTo n).

Definition largest_Grow_nat_of_depth (n : nat) : nat :=
  eval (largest_of_depth n).

(* Generic lower-bound lemma for our maxBy (copied from Contender). *)

Lemma maxBy_In {T : Type} :
  forall f (l : list T) currentMax currentBest,
    currentMax = f currentBest ->
    List.In (maxBy f currentMax currentBest l) l \/ maxBy f currentMax currentBest l = currentBest.
Proof.
  induction l; intros.
  - simpl. auto.
  - subst. simpl in *.
    destruct (f currentBest <? f a) eqn:E.
    + specialize (IHl (f a) _ eq_refl). firstorder congruence.
    + specialize (IHl (f currentBest) _ eq_refl). firstorder congruence.
Qed.

Lemma maxBy_at_least_currentMax {T : Type} :
  forall (f : T -> nat) l currentMax currentBest,
    f currentBest = currentMax ->
    currentMax <= f (maxBy f currentMax currentBest l).
Proof.
  induction l; intros; simpl in *.
  - lia.
  - subst. destruct (f currentBest <? f a) eqn:E.
    + apply Nat.ltb_lt in E.
      specialize (IHl (f a) _ eq_refl).
      lia.
    + apply Nat.ltb_ge in E.
      eapply IHl.
      reflexivity.
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
      destruct (f currentBest <? f x) eqn:E.
      * apply Nat.ltb_lt in E.
        eapply maxBy_at_least_currentMax.
        reflexivity.
      * apply Nat.ltb_ge in E.
        eapply Nat.le_trans. 1: eassumption.
        eapply maxBy_at_least_currentMax.
        reflexivity.
    + subst.
      destruct (f currentBest <? f a) eqn:E.
      * apply Nat.ltb_lt in E. eauto.
      * apply Nat.ltb_ge in E. eauto.
Qed.

(* -------------------------------------------------------------------- *)
(* Embedding from Contender.term into L_Grow + logical relation.         *)
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
Proof.
  induction t; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

Fixpoint RelVal (A : type) : interp_type A -> interp_type A -> Prop :=
  match A with
  | tpNat => fun x y => x = y
  | tpArr A1 A2 => fun f g => forall x y, RelVal A1 x y -> RelVal A2 (f x) (g y)
  end.

Definition RelPack (p q : pack) : Prop :=
  exists tp (v1 v2 : interp_type tp),
    p = existT Contender.interp_type tp v1
    /\ q = existT Contender.interp_type tp v2
    /\ RelVal tp v1 v2.

Definition RelEnv (e1 e2 : list pack) : Prop :=
  List.Forall2 RelPack e1 e2.

Lemma error_related : forall tp,
    RelVal tp (@error tp) (@error tp).
Proof.
  induction tp; simpl.
  - reflexivity.
  - intros x y _.
    exact IHtp2.
Qed.

Lemma RelPack_error :
  RelPack
    (existT Contender.interp_type tpNat (@error tpNat))
    (existT Contender.interp_type tpNat (@error tpNat)).
Proof.
  exists tpNat, (@error tpNat), (@error tpNat). split; [reflexivity|].
  split; [reflexivity|].
  simpl. reflexivity.
Qed.

Lemma Forall2_nth_error :
  forall {A B : Type} (R : A -> B -> Prop) l1 l2 n x,
    List.Forall2 R l1 l2 ->
    nth_error l1 n = Some x ->
    exists y, nth_error l2 n = Some y /\ R x y.
Proof.
  intros A B R l1 l2 n x H.
  revert n x.
  induction H; intros n x0 Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n; simpl in *.
    + inversion Hnth; subst. exists y. split; [reflexivity|assumption].
    + eauto.
Qed.

Lemma lookup_related_some :
  forall e1 e2 n p1,
    RelEnv e1 e2 ->
    Contender.lookup e1 n = Some p1 ->
    exists p2, Contender.lookup e2 n = Some p2 /\ RelPack p1 p2.
Proof.
  intros e1 e2 n p1 Henv Hlk.
  pose proof (List.Forall2_length Henv) as Hlen.
  (* Unfold lookup just enough to expose the [length e1 <=? n] branch. *)
  unfold Contender.lookup in Hlk.
  change
    ((if length e1 <=? n then None else nth_error e1 (length e1 - S n)) = Some p1)
    in Hlk.
  destruct (length e1 <=? n) eqn:E in Hlk.
  - discriminate Hlk.
  - (* Now [Hlk] is an [nth_error] fact at index [length e1 - S n]. *)
    (* Now [Hlk] is an [nth_error] fact at index [length e1 - S n]. *)
    eapply Forall2_nth_error in Henv. 2: exact Hlk.
    destruct Henv as [p2 [H2 HR]].
    exists p2. split; [|exact HR].
    unfold Contender.lookup.
    change
      ((if length e2 <=? n then None else nth_error e2 (length e2 - S n)) = Some p2).
    rewrite <- Hlen.
    rewrite E.
    exact H2.
Qed.

Lemma lookup_related_none :
  forall e1 e2 n,
    RelEnv e1 e2 ->
    Contender.lookup e1 n = None ->
    Contender.lookup e2 n = None.
Proof.
  intros e1 e2 n Henv Hlk.
  pose proof (List.Forall2_length Henv) as Hlen.
  unfold Contender.lookup in Hlk.
  change
    ((if length e1 <=? n then None else nth_error e1 (length e1 - S n)) = None)
    in Hlk.
  destruct (length e1 <=? n) eqn:E in Hlk.
  - unfold Contender.lookup.
    change
      ((if length e2 <=? n then None else nth_error e2 (length e2 - S n)) = None).
    rewrite <- Hlen.
    rewrite E.
    reflexivity.
  - (* Impossible: if [length e1 > n] then the computed index is in-bounds. *)
    simpl in Hlk.
    apply Nat.leb_gt in E.
    apply (proj1 (nth_error_None e1 (length e1 - S n))) in Hlk.
    assert (length e1 - S n < length e1) as Hlt.
    { apply Nat.sub_lt; lia. }
    lia.
Qed.

(* Past this point, treat lookup as opaque to keep simplification from
   expanding it into [length]/[nth_error] arithmetic during conversion. *)
Opaque Contender.lookup.

(* Relation-preservation of Contender.cast_impl (both directions). *)

Lemma cast_impl_related :
  forall from to,
    (forall (v1 v2 : interp_type from),
        RelVal from v1 v2 ->
        RelVal to (fst (Contender.cast_impl from to) v1) (fst (Contender.cast_impl from to) v2))
    /\
    (forall (u1 u2 : interp_type to),
        RelVal to u1 u2 ->
        RelVal from (snd (Contender.cast_impl from to) u1) (snd (Contender.cast_impl from to) u2)).
Proof.
  induction from; intros to; destruct to.
  - split; intros; assumption.
  - (* tpNat -> tpArr *)
    split.
    + intros v1 v2 Hv. simpl. intros x y Hxy.
      exact (error_related to2).
    + intros u1 u2 Hu. simpl. reflexivity.
  - (* tpArr -> tpNat *)
    split.
    + intros v1 v2 Hv. simpl. reflexivity.
    + intros u1 u2 Hu. simpl. intros x y Hxy.
      exact (error_related from2).
  - (* tpArr -> tpArr *)
    simpl.
    destruct (Contender.type_eqb from1 to1) eqn:E1;
    destruct (Contender.type_eqb from2 to2) eqn:E2; simpl.
    + destruct (IHfrom1 to1) as [IH1fw IH1bw].
      destruct (IHfrom2 to2) as [IH2fw IH2bw].
      split.
      * intros f1 f2 Hf. simpl. intros x y Hxy.
        destruct (Contender.cast_impl from1 to1) as [fw1 bw1] eqn:C1.
        destruct (Contender.cast_impl from2 to2) as [fw2 bw2] eqn:C2.
        simpl in *.
        eapply IH2fw.
        eapply Hf.
        eapply IH1bw.
        exact Hxy.
      * intros g1 g2 Hg. simpl. intros x y Hxy.
        destruct (Contender.cast_impl from1 to1) as [fw1 bw1] eqn:C1.
        destruct (Contender.cast_impl from2 to2) as [fw2 bw2] eqn:C2.
        simpl in *.
        eapply IH2bw.
        eapply Hg.
        eapply IH1fw.
        exact Hxy.
    + split.
      * intros f1 f2 Hf. simpl. intros x y Hxy.
        exact (error_related to2).
      * intros g1 g2 Hg. simpl. intros x y Hxy.
        exact (error_related from2).
    + split.
      * intros f1 f2 Hf. simpl. intros x y Hxy.
        exact (error_related to2).
      * intros g1 g2 Hg. simpl. intros x y Hxy.
        exact (error_related from2).
    + split.
      * intros f1 f2 Hf. simpl. intros x y Hxy.
        exact (error_related to2).
      * intros g1 g2 Hg. simpl. intros x y Hxy.
        exact (error_related from2).
Qed.

Lemma cast_impl_fw_related :
  forall from to (v1 v2 : interp_type from),
    RelVal from v1 v2 ->
    RelVal to (fst (Contender.cast_impl from to) v1) (fst (Contender.cast_impl from to) v2).
Proof.
  intros from to.
  exact (proj1 (cast_impl_related from to)).
Qed.

Lemma cast_impl_bw_related :
  forall from to (u1 u2 : interp_type to),
    RelVal to u1 u2 ->
    RelVal from (snd (Contender.cast_impl from to) u1) (snd (Contender.cast_impl from to) u2).
Proof.
  intros from to.
  exact (proj2 (cast_impl_related from to)).
Qed.

Lemma cast_related :
  forall from to (v1 v2 : interp_type from),
    RelVal from v1 v2 ->
    RelVal to (@cast from to v1) (@cast from to v2).
Proof.
  intros from to v1 v2 H.
  unfold cast.
  eapply cast_impl_fw_related; eassumption.
Qed.

Local Transparent Contender.lookup.

(* Self-contained reduction lemmas for the tVar case.  By proving them
   outside of the main induction, we avoid whatever interaction between
   [destruct ... eqn:] and the [Opaque] pragmas above is making
   in-place [rewrite] fail in the main proof. *)
Lemma Contender_interp_term_tVar_Some : forall e x p,
    Contender.lookup e x = Some p ->
    Contender.interp_term e (Contender.tVar x) = p.
Proof.
  intros e x p H. simpl. rewrite H. reflexivity.
Qed.

Lemma Contender_interp_term_tVar_None : forall e x,
    Contender.lookup e x = None ->
    Contender.interp_term e (Contender.tVar x)
    = existT Contender.interp_type tpNat (@error tpNat).
Proof.
  intros e x H. simpl. rewrite H. reflexivity.
Qed.

Lemma interp_term_tVar_Some : forall e x p,
    Contender.lookup e x = Some p ->
    interp_term e (tVar x) = p.
Proof.
  intros e x p H. simpl. rewrite H. reflexivity.
Qed.

Lemma interp_term_tVar_None : forall e x,
    Contender.lookup e x = None ->
    interp_term e (tVar x)
    = existT Contender.interp_type tpNat (@error tpNat).
Proof.
  intros e x H. simpl. rewrite H. reflexivity.
Qed.

Lemma embed_interp_related :
  forall e1 e2 t,
    RelEnv e1 e2 ->
    RelPack (Contender.interp_term e1 t) (interp_term e2 (embed_term t)).
Proof.
  intros e1 e2 t Henv.
  revert e1 e2 Henv.
  induction t as [x|A B body IH|t1 IH1 t2 IH2| | |R];
    intros e1 e2 Henv.
  - (* tVar.  After [simpl], both sides become
       [match Contender.lookup _ x with Some R => R | None => existT _ tpNat error end].
       [destruct (Contender.lookup e1 x) eqn:E1] substitutes the LHS
       match (so the goal's first conjunct becomes [p1 = ...]
       directly).  The RHS still mentions [Contender.lookup e2 x],
       which we substitute via [rewrite E2] using the
       [lookup_related_*] lemmas. *)
    cbn [embed_term].
    destruct (Contender.lookup e1 x) as [p1|] eqn:E1.
    + destruct (lookup_related_some e1 e2 x p1 Henv E1) as [p2 [E2 HR]].
      rewrite (Contender_interp_term_tVar_Some _ _ _ E1).
      rewrite (interp_term_tVar_Some _ _ _ E2).
      exact HR.
    + pose proof (lookup_related_none e1 e2 x Henv E1) as E2.
      rewrite (Contender_interp_term_tVar_None _ _ E1).
      rewrite (interp_term_tVar_None _ _ E2).
      exact RelPack_error.
  - (* tLam *)
    exists (tpArr A B).
    exists (projT2 (existT _ (tpArr A B)
                    (fun x' : interp_type A =>
                       cast B (projT2 (Contender.interp_term (existT _ A x' :: e1) body))))).
    exists (projT2 (existT _ (tpArr A B)
                    (fun x' : interp_type A =>
                       cast B (projT2 (interp_term (existT _ A x' :: e2) (embed_term body)))))).
    split; [reflexivity|].
    split; [reflexivity|].
    simpl.
    intros x y Hxy.
    specialize (IH (existT _ A x :: e1) (existT _ A y :: e2)).
    assert (RelEnv (existT _ A x :: e1) (existT _ A y :: e2)) as Henv'.
    { constructor.
      - exists A, x, y. split; [reflexivity|]. split; [reflexivity|]. exact Hxy.
      - exact Henv.
    }
    specialize (IH Henv').
    destruct IH as [tpb [rb1 [rb2 [Eold [Enew Hrb]]]]].
    rewrite Eold, Enew.
    simpl.
    apply cast_related.
    exact Hrb.
  - (* tApp *)
    cbn [Contender.interp_term interp_term embed_term].
    specialize (IH1 e1 e2 Henv).
    specialize (IH2 e1 e2 Henv).
    destruct IH1 as [tp1 [v1 [v1' [Htp1 [Htp1' Hrel1]]]]].
    destruct IH2 as [tp2 [v2 [v2' [Htp2 [Htp2' Hrel2]]]]].
    rewrite Htp1, Htp1', Htp2, Htp2'.
    simpl.
    destruct tp1 as [|A B].
    + (* tpNat: both error *)
      exact RelPack_error.
    + (* arrow *)
      exists B.
      exists (v1 (Contender.cast A v2)).
      exists (v1' (cast A v2')).
      split; [reflexivity|]. split; [reflexivity|].
      eapply Hrel1.
      eapply cast_related.
      exact Hrel2.
  - (* tO *)
    exists tpNat, 0, 0. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - (* tS *)
    exists (tpArr tpNat tpNat), S, S.
    split; [reflexivity|]. split; [reflexivity|].
    simpl. intros x y Hxy. subst. reflexivity.
  - (* tNatRec *)
    exists (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R))).
    exists (@Nat.recursion (interp_type R)).
    exists (@Nat.recursion (interp_type R)).
    split; [reflexivity|]. split; [reflexivity|].
    (* Nat.recursion respects the logical relation. *)
    simpl.
    intros base1 base2 Hbase.
    intros step1 step2 Hstep.
    intros n1 n2 Hn.
    subst n2.
    revert base1 base2 Hbase step1 step2 Hstep.
    induction n1; intros; simpl.
    + exact Hbase.
    + eapply Hstep.
      * reflexivity.
      * apply IHn1; assumption.
Qed.

(* embed_eval needs to peek inside [Contender.eval] (which is otherwise
   kept Opaque to keep the kernel from running depth-bounded searches).
   We expose it just for this lemma and re-mark it Opaque afterwards. *)
Local Transparent Contender.eval.

Lemma embed_eval : forall t,
    eval (embed_term t) = Contender.eval t.
Proof.
  intro t.
  pose proof (embed_interp_related [] [] t (List.Forall2_nil _)) as H.
  destruct H as [tp [v1 [v2 [Hp1 [Hp2 Hrel]]]]].
  unfold eval, Contender.eval.
  replace (Contender.interp_term [] t)
    with (existT Contender.interp_type tp v1) by (symmetry; exact Hp1).
  replace (interp_term [] (embed_term t))
    with (existT Contender.interp_type tp v2) by (symmetry; exact Hp2).
  simpl.
  destruct tp; [symmetry; exact Hrel | reflexivity].
Qed.

Local Opaque Contender.eval.

(* -------------------------------------------------------------------- *)
(* Main theorems: explicit lower bound and strict inequality.            *)
(* -------------------------------------------------------------------- *)

Definition contender_grow_6 : nat := largest_Grow_nat_of_depth 44.

(* The next two lemmas need to peek inside Contender's opaque
   definitions (they need [largest_STLCNatRec_nat_of_depth = eval
   (largest_of_depth ...)] etc.).  Restore transparency just for them
   and re-mark Opaque afterwards. *)
Local Transparent Contender.largest_STLCNatRec_nat_of_depth.
Local Transparent Contender.largest_of_depth.
Local Transparent Contender.eval.

Lemma contender_5_ge_1 : 1 <= Contender.contender_5.
Proof.
  unfold Contender.contender_5, Contender.largest_STLCNatRec_nat_of_depth.
  unfold Contender.largest_of_depth.
  (* Witness term: S 0 = 1 is in termsUpTo 42. *)
  pose (one := Contender.tApp Contender.tS Contender.tO).
  assert (Hone_in : List.In one (Contender.termsUpTo 42)).
  { apply (proj1 (Contender.termsUpTo_correct 42 one)).
    subst one. cbv [Contender.term_depth Contender.nat_depth Contender.type_depth]. lia. }
  assert (Hone_eval : Contender.eval one = 1).
  { subst one. unfold Contender.eval. cbv. reflexivity. }
  (* lowerbound_maxBy gives eval one <= eval (maxBy ... termsUpTo 42). *)
  eapply Nat.le_trans. 1: exact (eq_ind_r (fun k => k <= _) (le_n 1) Hone_eval).
  eapply Contender.lowerbound_maxBy with (x := one). 2: reflexivity.
  exact Hone_in.
Qed.

Lemma exists_maximizer_42 :
  exists tstar : Contender.term,
    Contender.term_depth tstar <= 42 /\
    Contender.eval tstar = Contender.contender_5.
Proof.
  exists (Contender.largest_of_depth 42).
  split.
  - (* depth bound via maxBy_In + contender_5_ge_1 *)
    pose proof (Contender.maxBy_In Contender.eval (Contender.termsUpTo 42) 0 Contender.tO eq_refl) as P.
    destruct P as [Pin | Peq].
    + apply (proj2 (Contender.termsUpTo_correct 42 _)) in Pin.
      exact Pin.
    + (* Peq: largest_of_depth 42 = tO.  But contender_5 = eval (largest_of_depth 42) >= 1
         and eval tO = 0, contradiction. *)
      exfalso.
      pose proof contender_5_ge_1 as Hge.
      unfold Contender.contender_5,
             Contender.largest_STLCNatRec_nat_of_depth,
             Contender.largest_of_depth in Hge.
      rewrite Peq in Hge.
      unfold Contender.eval in Hge. cbn in Hge. lia.
  - unfold Contender.contender_5, Contender.largest_STLCNatRec_nat_of_depth.
    reflexivity.
Qed.

Definition witness_grow (tstar : Contender.term) : term :=
  tApp tGrow (tApp tS (embed_term tstar)).

Lemma witness_grow_depth :
  forall tstar,
    Contender.term_depth tstar <= 42 ->
    term_depth (witness_grow tstar) <= 44.
Proof.
  intros tstar H.
  unfold witness_grow.
  simpl.
  rewrite term_depth_embed.
  (* simpl unfolded [Nat.max 1 X] into a [match X with 0 => 1 | S _ => S _]
     case, which [lia] handles by destructing the depth. *)
  destruct (Contender.term_depth tstar) as [|n]; simpl; lia.
Qed.

Lemma witness_grow_eval :
  forall tstar,
    Contender.eval tstar = Contender.contender_5 ->
    eval (witness_grow tstar) = G.grow (S Contender.contender_5).
Proof.
  intros tstar Heq.
  unfold witness_grow.
  (* Get the exact nat-typed interpretation of the embedded maximizer. *)
  assert (eval (embed_term tstar) = Contender.contender_5) as Hembed.
  { rewrite embed_eval. exact Heq. }
  assert (1 <= eval (embed_term tstar)) as Hpos.
  { rewrite Hembed. exact contender_5_ge_1. }
  (* Destruct the interp_term result.  The eqn:E equation lets us
     compute what eval reduces to in each case. *)
  destruct (interp_term [] (embed_term tstar)) as [tp res] eqn:E.
  unfold eval in Hembed, Hpos. rewrite E in Hembed, Hpos.
  destruct tp as [|A B].
  - (* tpNat: Hembed says res = contender_5. *)
    simpl in Hembed. subst res.
    (* First: tS (embed tstar) evaluates to S contender_5. *)
    assert (interp_term [] (tApp tS (embed_term tstar))
            = existT _ tpNat (S Contender.contender_5)) as ES.
    { eapply interp_tApp_nat.
      - apply interp_tS.
      - exact E. }
    (* Second: tGrow applied to that. *)
    assert (interp_term [] (tApp tGrow (tApp tS (embed_term tstar)))
            = existT _ tpNat (G.grow (S Contender.contender_5))) as EG.
    { eapply interp_tApp_nat.
      - apply interp_tGrow.
      - exact ES. }
    unfold eval. rewrite EG. reflexivity.
  - (* arrow type: eval = 0 contradicts contender_5 >= 1. *)
    simpl in Hpos. lia.
Qed.

Theorem grow_lower_bound :
  G.grow (S Contender.contender_5) <= contender_grow_6.
Proof.
  unfold contender_grow_6, largest_Grow_nat_of_depth, largest_of_depth.
  destruct exists_maximizer_42 as [tstar [Hdepth Heval]].
  rewrite <- (witness_grow_eval tstar Heval).
  eapply lowerbound_maxBy with (x := witness_grow tstar). 2: reflexivity.
  apply (proj1 (termsUpTo_correct 44 (witness_grow tstar))).
  apply witness_grow_depth. exact Hdepth.
Qed.

Theorem contender_5_lt_contender_grow_6 :
  Contender.contender_5 < contender_grow_6.
Proof.
  eapply Nat.lt_le_trans with (m := G.grow (S Contender.contender_5)).
  - apply G.grow_gt_S.
  - exact grow_lower_bound.
Qed.

Print Assumptions grow_lower_bound.
Print Assumptions contender_5_lt_contender_grow_6.

End GrowEmbed.

Module BigGrowSig <: GrowSig.
  Definition grow := sandbox.Brouwer.BigGrow.
  Definition grow_gt_S : forall n, n < grow (S n) := sandbox.Brouwer.BigGrow_gt_S.
End BigGrowSig.

Module BigGrowEmbed := GrowEmbed(BigGrowSig).

(* Named instances for grep/search from other sandboxes. *)
Definition contender_grow_6 : nat := BigGrowEmbed.contender_grow_6.

Definition BigGrow_lower_bound :
    sandbox.Brouwer.BigGrow (S Contender.contender_5) <= contender_grow_6
  := BigGrowEmbed.grow_lower_bound.

Definition contender_5_lt_contender_grow_6 :
    Contender.contender_5 < contender_grow_6
  := BigGrowEmbed.contender_5_lt_contender_grow_6.

Print Assumptions BigGrow_lower_bound.
Print Assumptions contender_5_lt_contender_grow_6.

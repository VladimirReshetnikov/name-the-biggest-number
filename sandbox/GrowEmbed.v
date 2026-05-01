(* Sandbox: Approach M -- embedding-witness fresh-engine shell.

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

       and hence the strict inequality contender_5 < contender_grow_6,
       assuming grow_gt_S : forall n, n < grow (S n).

   Compile from repo root, after Contender.vo and sandbox/Brouwer.vo exist:

     coqc -Q . "" sandbox\GrowEmbed.v
*)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

Require Contender.
Require Import sandbox.Brouwer.

(* Coq kernel conversion must never try to unfold depth-bounded search at a
   concrete depth like 42.  Keep Contender's max/search machinery opaque in
   this file.  (We only use its lemmas about these constants.) *)
Opaque Contender.eval Contender.maxBy Contender.termsUpTo Contender.typesUpTo
       Contender.natsUpTo Contender.largest_of_depth
       Contender.largest_STLCNatRec_nat_of_depth.

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

Fixpoint term_depth (t : term) : nat :=
  match t with
  | tVar x => S (Contender.nat_depth x)
  | tLam A B body =>
      S (max (max (Contender.type_depth A) (Contender.type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (Contender.type_depth R)
  | tGrow => 1
  end.

Definition error {tp : type} : interp_type tp := Contender.error (tp := tp).
Definition cast {from : type} (to : type) : interp_type from -> interp_type to :=
  Contender.cast (from := from) to.

(* Tactic-style [refine] is unnecessary here: a direct [Fixpoint]
   definition is more readable and slightly shorter. *)
Fixpoint interp_term (e : list pack) (t : term) : pack :=
  match t with
  | tVar x =>
      match Contender.lookup e x with
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
  | tGrow    => existT _ (tpArr tpNat tpNat) G.grow
  end.

Definition eval (t : term) : nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat => fun res : interp_type tpNat => res
  | tpArr _ _ => fun _ => 0
  end res.

(* -------------------------------------------------------------------- *)
(* Enumeration for L_Grow: copy Contender's depth-bounded generator and  *)
(* add the new constant [tGrow].                                        *)
(* -------------------------------------------------------------------- *)

Fixpoint termsUpTo (n : nat) : list term :=
  match n with
  | O => []
  | S m =>
    List.map tVar (Contender.natsUpTo m) ++
    List.map (fun '(A, B, body) => tLam A B body)
             (list_prod (list_prod (Contender.typesUpTo m) (Contender.typesUpTo m)) (termsUpTo m)) ++
    List.map (fun '(t1, t2) => tApp t1 t2)
             (list_prod (termsUpTo m) (termsUpTo m)) ++
    [tO] ++ [tS] ++
    List.map tNatRec (Contender.typesUpTo m) ++
    [tGrow]
  end.

(* Forward helper: discharge an [In _ (map _ _)] / [In _ (list_prod _ _)]
   obligation by repeatedly peeling off [in_map] / [in_prod] and discharging
   side conditions via the correctness lemmas plus an in-scope [IHn]. *)
Ltac termsUpTo_solve_in IHn :=
  repeat first
    [ apply in_map | apply in_prod
    | apply (proj1 (Contender.natsUpTo_correct _ _))
    | apply (proj1 (Contender.typesUpTo_correct _ _))
    | apply (proj1 (IHn _))
    | lia].

(* Backward helper: convert all [In _ (natsUpTo _ / typesUpTo _ / termsUpTo _)]
   hypotheses into depth bounds via the correctness lemmas, then close by
   [simpl; lia]. *)
Ltac termsUpTo_depth_lia IHn :=
  repeat match goal with
  | H : List.In _ (Contender.natsUpTo _)  |- _ => apply (proj2 (Contender.natsUpTo_correct  _ _)) in H
  | H : List.In _ (Contender.typesUpTo _) |- _ => apply (proj2 (Contender.typesUpTo_correct _ _)) in H
  | H : List.In _ (termsUpTo _) |- _ => apply (proj2 (IHn _)) in H
  end;
  simpl; lia.

Lemma termsUpTo_correct : forall n t,
    term_depth t <= n <-> List.In t (termsUpTo n).
Proof.
  (* The forward direction navigates to the correct ++ slot per constructor
     and proves membership using [termsUpTo_solve_in IHn]; the backward
     direction destructs the list-of-append-segments and reads off depth
     bounds. *)
  induction n; intros; split; intros.
  - destruct t; simpl in *; lia.
  - simpl in *. contradiction.
  - destruct t; simpl in *.
    + do 0 (apply in_or_app; right). apply in_or_app; left.
      termsUpTo_solve_in IHn.
    + do 1 (apply in_or_app; right). apply in_or_app; left.
      match goal with |- In ?e (map ?f _) => change e with (f (A, B, t)) end.
      termsUpTo_solve_in IHn.
    + do 2 (apply in_or_app; right). apply in_or_app; left.
      match goal with |- In ?e (map ?f _) => change e with (f (t1, t2)) end.
      termsUpTo_solve_in IHn.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. right. right.
      apply in_app_iff; left. termsUpTo_solve_in IHn.
    + do 3 (apply in_or_app; right). simpl. right. right.
      apply in_app_iff; right. simpl. auto.
  - (* Backward: split [t] across the [++] segments, then for each segment
       extract the pre-image (if any) of [List.map] / [list_prod] and use
       [termsUpTo_depth_lia] to read off depth bounds via the correctness
       lemmas of [natsUpTo] / [typesUpTo] and the IH. *)
    simpl in *.
    repeat ((simpl in H || apply in_app_iff in H || idtac); destruct H).
    + apply in_map_iff in H as (x & ? & H); subst t. termsUpTo_depth_lia IHn.
    + apply in_map_iff in H as ([[A B] body] & ? & H); subst t.
      repeat (apply in_prod_iff in H; destruct H). termsUpTo_depth_lia IHn.
    + apply in_map_iff in H as ([t1 t2] & ? & H); subst t.
      repeat (apply in_prod_iff in H; destruct H). termsUpTo_depth_lia IHn.
    + simpl. lia.
    + simpl. lia.
    + apply in_map_iff in H as (R & ? & H); subst t. termsUpTo_depth_lia IHn.
    + simpl. lia.
Qed.

(* [maxBy] and its standard lemmas are polymorphic over the element
   type, so we reuse Contender's definitions verbatim rather than
   re-defining them.  [Contender.maxBy] is kept Opaque file-wide
   (above) -- only its public lemmas are needed. *)

Definition largest_of_depth (n : nat) : term :=
  Contender.maxBy eval 0 tO (termsUpTo n).

Definition largest_Grow_nat_of_depth (n : nat) : nat :=
  eval (largest_of_depth n).

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
Proof. induction t; simpl; congruence. Qed.

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

(* Convenience constructor for [RelPack] when both packs are explicit. *)
Lemma RelPack_intro :
  forall tp (v1 v2 : interp_type tp),
    RelVal tp v1 v2 ->
    RelPack (existT Contender.interp_type tp v1) (existT Contender.interp_type tp v2).
Proof. intros tp v1 v2 H; exists tp, v1, v2; repeat split; assumption. Qed.

Definition RelEnv (e1 e2 : list pack) : Prop :=
  List.Forall2 RelPack e1 e2.

Lemma error_related : forall tp, RelVal tp (@error tp) (@error tp).
Proof. induction tp; simpl; [reflexivity | intros _ _ _; exact IHtp2]. Qed.

Lemma RelPack_error :
  RelPack
    (existT Contender.interp_type tpNat (@error tpNat))
    (existT Contender.interp_type tpNat (@error tpNat)).
Proof. apply RelPack_intro; reflexivity. Qed.

Lemma Forall2_nth_error :
  forall {A B : Type} (R : A -> B -> Prop) l1 l2 n x,
    List.Forall2 R l1 l2 ->
    nth_error l1 n = Some x ->
    exists y, nth_error l2 n = Some y /\ R x y.
Proof.
  intros * H; revert n x; induction H; intros [|n] x0 Hnth; simpl in *;
    [discriminate|discriminate|inversion Hnth; subst; eauto|eauto].
Qed.

(* Since [RelEnv] is [Forall2], both environments have the same length.
   Contender's reverse-indexed [lookup] therefore either misses on both sides
   or finds related entries at the same underlying [nth_error] index. *)
Lemma lookup_related :
  forall e1 e2 n,
    RelEnv e1 e2 ->
    match Contender.lookup e1 n, Contender.lookup e2 n with
    | Some p1, Some p2 => RelPack p1 p2
    | None, None => True
    | _, _ => False
    end.
Proof.
  intros e1 e2 n Henv.
  pose proof (List.Forall2_length Henv) as Hlen.
  unfold Contender.lookup. cbv zeta. rewrite Hlen.
  destruct (length e2 <=? n) eqn:E; [exact I|].
  destruct (nth_error e1 (length e2 - S n)) as [p1|] eqn:E1.
  - eapply Forall2_nth_error in Henv as (p2 & E2 & HR);
      [rewrite E2; exact HR | exact E1].
  - apply Nat.leb_gt in E.
    apply (proj1 (nth_error_None _ _)) in E1; lia.
Qed.

(* Past this point, treat lookup as opaque to keep simplification from
   expanding it into [length]/[nth_error] arithmetic during conversion. *)
Opaque Contender.lookup.

(* [cast_impl from to] is related to itself (in both directions) when
   inputs are related.  Both directions have to be done together because
   the [tpArr -> tpArr] case casts the function argument *backward*. *)

Lemma cast_impl_related : forall from to,
    (forall v1 v2,
        RelVal from v1 v2 ->
        RelVal to (fst (Contender.cast_impl from to) v1)
                  (fst (Contender.cast_impl from to) v2))
    /\
    (forall u1 u2,
        RelVal to u1 u2 ->
        RelVal from (snd (Contender.cast_impl from to) u1)
                    (snd (Contender.cast_impl from to) u2)).
Proof.
  (* tpNat/tpNat: cast is the identity.  tpNat/tpArr and tpArr/tpNat both
     fall to [error_related] in both directions.  Only tpArr/tpArr has a
     non-trivial recursive argument. *)
  induction from as [|from1 IH1 from2 IH2]; intros [|to1 to2]; simpl;
    try (split; intros; assumption);
    try (split; intros _ _ _; simpl;
         (reflexivity || (intros; apply error_related))).
  (* tpArr / tpArr: when both type_eqb match, recurse; otherwise error. *)
  destruct (Contender.type_eqb from1 to1) eqn:E1;
  destruct (Contender.type_eqb from2 to2) eqn:E2; simpl;
    try (split; intros _ _ _; simpl; intros; apply error_related).
  destruct (IH1 to1) as [IH1fw IH1bw], (IH2 to2) as [IH2fw IH2bw].
  destruct (Contender.cast_impl from1 to1) eqn:C1.
  destruct (Contender.cast_impl from2 to2) eqn:C2.
  split; intros f g Hfg x y Hxy; simpl in *.
  - apply IH2fw. apply Hfg. apply IH1bw. exact Hxy.
  - apply IH2bw. apply Hfg. apply IH1fw. exact Hxy.
Qed.

Lemma cast_related : forall from to v1 v2,
    RelVal from v1 v2 ->
    RelVal to (@cast from to v1) (@cast from to v2).
Proof. intros; apply (proj1 (cast_impl_related _ _)); assumption. Qed.

Lemma embed_interp_related :
  forall e1 e2 t,
    RelEnv e1 e2 ->
    RelPack (Contender.interp_term e1 t) (interp_term e2 (embed_term t)).
Proof.
  intros e1 e2 t Henv.
  revert e1 e2 Henv.
  induction t as [x|A B body IH|t1 IH1 t2 IH2| | |R];
    intros e1 e2 Henv.
  - (* tVar.  Make both sides explicit [match lookup] expressions, then
       [lookup_related] rules out the one-sided cases. *)
    change
      (RelPack
         (match Contender.lookup e1 x with
          | Some p => p
          | None => existT Contender.interp_type tpNat (@error tpNat)
          end)
         (match Contender.lookup e2 x with
          | Some p => p
          | None => existT Contender.interp_type tpNat (@error tpNat)
          end)).
    pose proof (lookup_related e1 e2 x Henv) as Hlk.
    destruct (Contender.lookup e1 x), (Contender.lookup e2 x);
      simpl in Hlk; try contradiction.
    + exact Hlk.
    + exact RelPack_error.
  - (* tLam.  Build the [tpArr]-typed RelPack directly (the explicit packs
       avoid any reliance on function extensionality); the IH gives a
       related body for any related extension of the environment. *)
    change
      (RelPack
         (existT Contender.interp_type (tpArr A B)
            (fun x' : interp_type A =>
               cast B (projT2 (Contender.interp_term (existT _ A x' :: e1) body))))
         (existT Contender.interp_type (tpArr A B)
            (fun x' : interp_type A =>
               cast B (projT2 (interp_term (existT _ A x' :: e2) (embed_term body)))))).
    apply RelPack_intro. simpl. intros x y Hxy.
    assert (RelEnv (existT _ A x :: e1) (existT _ A y :: e2)) as Henv'.
    { constructor; [|exact Henv]. apply RelPack_intro. exact Hxy. }
    destruct (IH _ _ Henv') as (tpb & rb1 & rb2 & Eold & Enew & Hrb).
    rewrite Eold, Enew. simpl. apply cast_related, Hrb.
  - (* tApp.  Both interp_term calls reduce to a [match] on the
       argument-1 type; if it's [tpArr A B] we get a function we can
       relate via the IH; otherwise both fall to [error]. *)
    cbn [Contender.interp_term interp_term embed_term].
    destruct (IH1 _ _ Henv) as (tp1 & v1 & v1' & Htp1 & Htp1' & Hrel1).
    destruct (IH2 _ _ Henv) as (tp2 & v2 & v2' & Htp2 & Htp2' & Hrel2).
    rewrite Htp1, Htp1', Htp2, Htp2'. simpl.
    destruct tp1 as [|A B]; [exact RelPack_error|].
    apply RelPack_intro. apply Hrel1, cast_related, Hrel2.
  - (* tO *)
    apply RelPack_intro. reflexivity.
  - (* tS *)
    apply RelPack_intro. simpl. intros x y Hxy. subst. reflexivity.
  - (* tNatRec.  [Nat.recursion] respects the logical relation: equal
       counters + related base/step give related accumulators. *)
    apply RelPack_intro. simpl.
    intros base1 base2 Hbase step1 step2 Hstep n1 n2 Hn. subst n2.
    induction n1 in base1, base2, Hbase, step1, step2, Hstep |- *; simpl;
      [exact Hbase | apply Hstep; [reflexivity | apply IHn1; assumption]].
Qed.

(* embed_eval needs to peek inside [Contender.eval] (which is otherwise
   kept Opaque to keep the kernel from running depth-bounded searches).
   We expose it just for this lemma and re-mark it Opaque afterwards. *)
Local Transparent Contender.eval.

Lemma embed_eval : forall t,
    eval (embed_term t) = Contender.eval t.
Proof.
  intro t.
  pose proof (embed_interp_related [] [] t (List.Forall2_nil _))
    as (tp & v1 & v2 & Hp1 & Hp2 & Hrel).
  unfold eval, Contender.eval.
  replace (Contender.interp_term nil t) with (existT Contender.interp_type tp v1)
    by (symmetry; exact Hp1).
  replace (interp_term nil (embed_term t)) with (existT Contender.interp_type tp v2)
    by (symmetry; exact Hp2).
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
Local Transparent Contender.largest_STLCNatRec_nat_of_depth
                  Contender.largest_of_depth Contender.eval.

(* [contender_5 >= 1] because [tApp tS tO] is in [termsUpTo 42] and
   evaluates to 1.  [Contender.lowerbound_maxBy] does the rest. *)
Lemma contender_5_ge_1 : 1 <= Contender.contender_5.
Proof.
  unfold Contender.contender_5, Contender.largest_STLCNatRec_nat_of_depth,
         Contender.largest_of_depth.
  change 1 with (Contender.eval (Contender.tApp Contender.tS Contender.tO)).
  apply Contender.lowerbound_maxBy
    with (x := Contender.tApp Contender.tS Contender.tO);
    [apply (proj1 (Contender.termsUpTo_correct 42 _)); cbv; lia | reflexivity].
Qed.

(* The maximizer term *t* whose eval realises [contender_5].  Either
   [maxBy] returned a member of [termsUpTo 42] (depth bound is direct)
   or it returned the initial best [tO] -- but that contradicts
   [contender_5_ge_1]. *)
Lemma exists_maximizer_42 :
  exists tstar : Contender.term,
    Contender.term_depth tstar <= 42 /\
    Contender.eval tstar = Contender.contender_5.
Proof.
  pose proof contender_5_ge_1 as Hge.
  unfold Contender.contender_5, Contender.largest_STLCNatRec_nat_of_depth,
         Contender.largest_of_depth in *.
  exists (Contender.maxBy Contender.eval 0 Contender.tO (Contender.termsUpTo 42));
    split; [|reflexivity].
  destruct (Contender.maxBy_In Contender.eval (Contender.termsUpTo 42)
                               0 Contender.tO eq_refl) as [Pin | Peq].
  - apply (proj2 (Contender.termsUpTo_correct 42 _)) in Pin. exact Pin.
  - (* Peq: maxBy ... = tO.  Then contender_5 = eval tO = 0, contradicting >= 1. *)
    rewrite Peq in Hge. cbv in Hge. lia.
Qed.

Definition witness_grow (tstar : Contender.term) : term :=
  tApp tGrow (tApp tS (embed_term tstar)).

Lemma witness_grow_depth :
  forall tstar,
    Contender.term_depth tstar <= 42 ->
    term_depth (witness_grow tstar) <= 44.
Proof.
  intros tstar H. unfold witness_grow. simpl. rewrite term_depth_embed.
  (* [simpl] unfolded [Nat.max 1 X] into a [match X with 0 | S _ end] case;
     destructing the depth lets [lia] close both branches. *)
  destruct (Contender.term_depth tstar); simpl; lia.
Qed.

Lemma witness_grow_eval :
  forall tstar,
    Contender.eval tstar = Contender.contender_5 ->
    eval (witness_grow tstar) = G.grow (S Contender.contender_5).
Proof.
  intros tstar Heq.
  (* The embedded maximizer is a closed term of type [tpNat] computing [contender_5]. *)
  assert (Hembed : eval (embed_term tstar) = Contender.contender_5)
    by (rewrite embed_eval; exact Heq).
  unfold witness_grow, eval in *.
  destruct (interp_term [] (embed_term tstar)) as [[|A B] res] eqn:E;
    simpl in Hembed.
  - (* [tpNat]: compute both nested [tApp]s by unfolding [interp_term],
       rewriting the stuck inner [interp_term] using [E], then [cbn]. *)
    subst res. cbn [interp_term]; rewrite E; cbn [interp_term]; reflexivity.
  - (* Arrow type: [eval = 0] contradicts [contender_5 >= 1]. *)
    pose proof contender_5_ge_1; lia.
Qed.

Theorem grow_lower_bound :
  G.grow (S Contender.contender_5) <= contender_grow_6.
Proof.
  unfold contender_grow_6, largest_Grow_nat_of_depth, largest_of_depth.
  destruct exists_maximizer_42 as (tstar & Hdepth & Heval).
  rewrite <- (witness_grow_eval tstar Heval).
  eapply Contender.lowerbound_maxBy with (x := witness_grow tstar). 2: reflexivity.
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

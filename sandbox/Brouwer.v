(* Sandbox: Brouwer ordinal notations and the fast-growing hierarchy at
   ordinals up to (and through) epsilon_0.

   This is a fresh axis of "next contender" exploration, complementing the
   reflection-tower track (Approach D in IDEAS.md, now saturated through D.3
   at depth 23) and addressing the blocker noted for Approach A:

   IDEAS.md says Approach A's main open question is well-founded recursion
   on Cantor Normal Form ordinals.  Brouwer ordinals sidestep that question
   entirely by making the fundamental sequence *part of the data* of every
   limit ordinal:

       Inductive Brouwer :=
       | Bz   : Brouwer
       | Bsucc: Brouwer -> Brouwer
       | Blim : (nat -> Brouwer) -> Brouwer.

   With this presentation, [Fixpoint] over Brouwer ordinals is
   *structurally* total -- any recursive call [f n] inside a [Blim f] case
   is a strict subterm by Coq's W-type guard, so [FGH], [Hardy], and the
   ordinal arithmetic operations all go through with no [Acc], no [Fix],
   no fuel parameter.

   What this file delivers:
   * Brouwer ordinal type and basic constants (omega, omega_omega, ...).
   * Total Brouwer ordinal addition, multiplication, and omega-exponentiation.
   * A definition of [epsilon_0 : Brouwer] as the limit of the omega-tower.
   * The fast-growing hierarchy [FGH : Brouwer -> nat -> nat] and Hardy
     hierarchy [Hardy : Brouwer -> nat -> nat], both as plain [Fixpoint]s.
   * Sanity checks at small ordinals.
   * Notes on the next step: a contender language with a [tFGH] primitive
     interpreted as [FGH epsilon_0].

   Compile from repo root:

     coqc -Q . "" sandbox\Brouwer.v
*)

Require Import Arith Lia.

(* -------------------------------------------------------------------- *)
(* Brouwer ordinal notations.                                            *)
(*                                                                       *)
(*   Bz             stands for the ordinal 0.                            *)
(*   Bsucc a        stands for a + 1.                                    *)
(*   Blim f         stands for the supremum of {f 0, f 1, f 2, ...}.     *)
(*                                                                       *)
(* These are *notations*, not ordinals up to extensional equality:       *)
(* different f's that converge to the same supremum are different        *)
(* Brouwer terms.  But for fast-growing-hierarchy purposes the choice    *)
(* of fundamental sequence is exactly what we want to commit to anyway.  *)
(* -------------------------------------------------------------------- *)

Inductive Brouwer : Type :=
| Bz    : Brouwer
| Bsucc : Brouwer -> Brouwer
| Blim  : (nat -> Brouwer) -> Brouwer.

(* Embedding nat -> Brouwer as an iterated successor. *)
Fixpoint nat_to_B (n : nat) : Brouwer :=
  match n with
  | 0 => Bz
  | S n' => Bsucc (nat_to_B n')
  end.

Definition one : Brouwer := Bsucc Bz.
Definition two : Brouwer := Bsucc one.

(* The first limit ordinal omega = sup_n n. *)
Definition omega : Brouwer := Blim nat_to_B.

(* -------------------------------------------------------------------- *)
(* Ordinal arithmetic on Brouwer notations.                              *)
(*                                                                       *)
(*   Each fixpoint recurses structurally on its second argument. *)
(* -------------------------------------------------------------------- *)

Fixpoint Badd (a b : Brouwer) : Brouwer :=
  match b with
  | Bz       => a
  | Bsucc b' => Bsucc (Badd a b')
  | Blim f   => Blim (fun n => Badd a (f n))
  end.

Fixpoint Bmul (a b : Brouwer) : Brouwer :=
  match b with
  | Bz       => Bz
  | Bsucc b' => Badd (Bmul a b') a
  | Blim f   => Blim (fun n => Bmul a (f n))
  end.

(* omega^a, by induction on a. *)
Fixpoint omega_pow (a : Brouwer) : Brouwer :=
  match a with
  | Bz       => one                                       (* omega^0 = 1 *)
  | Bsucc a' => Bmul (omega_pow a') omega                 (* omega^(a+1) = omega^a * omega *)
  | Blim f   => Blim (fun n => omega_pow (f n))           (* omega^(lim f) = lim_n (omega^(f n)) *)
  end.

(* The omega-tower: omega_tower 0 = 1, omega_tower (S n) = omega^(omega_tower n).
   So omega_tower n is omega ^^ n in tetration notation. *)
Fixpoint omega_tower (n : nat) : Brouwer :=
  match n with
  | 0    => one
  | S n' => omega_pow (omega_tower n')
  end.

(* epsilon_0 = sup_n (omega ^^ n).  This is the proof-theoretic ordinal of
   Peano arithmetic, and the natural ceiling for STLC+NatRec / System T. *)
Definition epsilon_0 : Brouwer := Blim omega_tower.

(* -------------------------------------------------------------------- *)
(* The fast-growing hierarchy.                                           *)
(*                                                                       *)
(*   f_0(n)         = n + 1.                                             *)
(*   f_{a+1}(n)     = f_a iterated n times starting from n.              *)
(*   f_lambda(n)    = f_{lambda[n]}(n)  where lambda[n] is the n-th term *)
(*                    of the fundamental sequence at the limit lambda.   *)
(*                                                                       *)
(* On Brouwer notations the fundamental sequence is just the function    *)
(* stored in the [Blim] constructor, so the limit case is trivially      *)
(* structural. *)
(* -------------------------------------------------------------------- *)

Fixpoint FGH (a : Brouwer) (n : nat) : nat :=
  match a with
  | Bz       => S n
  | Bsucc a' => Nat.iter n (FGH a') n
  | Blim f   => FGH (f n) n
  end.

(* Hardy hierarchy.  Slower-growing sibling of FGH: H_0 = id,
   H_{a+1}(n) = H_a(n+1), H_lambda(n) = H_{lambda[n]}(n). *)
Fixpoint Hardy (a : Brouwer) (n : nat) : nat :=
  match a with
  | Bz       => n
  | Bsucc a' => Hardy a' (S n)
  | Blim f   => Hardy (f n) n
  end.

(* -------------------------------------------------------------------- *)
(* Small structural lemmas connecting FGH at small Brouwer ordinals to   *)
(* familiar arithmetic.  All proofs are short and use no axioms.         *)
(* -------------------------------------------------------------------- *)

Lemma FGH_Bz_eq : forall n, FGH Bz n = S n.
Proof. intro. reflexivity. Qed.

Lemma Nat_iter_FGH_Bz : forall n m, Nat.iter n (FGH Bz) m = n + m.
Proof.
  induction n; intros m; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma FGH_one_eq : forall n, FGH one n = 2 * n.
Proof.
  intro n.
  unfold one. cbn. rewrite Nat_iter_FGH_Bz. lia.
Qed.

(* By definition, FGH on a successor ordinal is iterated FGH on the
   predecessor.  Recorded explicitly because [reflexivity] alone does not
   make the pattern visually obvious. *)
Lemma FGH_Bsucc : forall a n, FGH (Bsucc a) n = Nat.iter n (FGH a) n.
Proof. intros. reflexivity. Qed.

Lemma FGH_Blim : forall f n, FGH (Blim f) n = FGH (f n) n.
Proof. intros. reflexivity. Qed.

(* Hardy variants of the same. *)
Lemma Hardy_Bz_eq : forall n, Hardy Bz n = n.
Proof. intro. reflexivity. Qed.

Lemma Hardy_Bsucc : forall a n, Hardy (Bsucc a) n = Hardy a (S n).
Proof. intros. reflexivity. Qed.

Lemma Hardy_Blim : forall f n, Hardy (Blim f) n = Hardy (f n) n.
Proof. intros. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(* Sanity checks at small ordinals.                                      *)
(* -------------------------------------------------------------------- *)

(* Finite ordinals: FGH (nat_to_B k) n = f_k(n). *)

Eval vm_compute in (FGH (nat_to_B 0) 10).      (* f_0(10) = 11 *)
Eval vm_compute in (FGH (nat_to_B 1) 10).      (* f_1(10) = 20 *)
Eval vm_compute in (FGH (nat_to_B 2) 4).       (* f_2(4) = 64 *)
Eval vm_compute in (FGH (nat_to_B 2) 6).       (* f_2(6) = 384 *)
Eval vm_compute in (FGH (nat_to_B 3) 2).       (* f_3(2) = 2048 *)

(* The first limit ordinal: f_omega(n) = f_n(n). *)
Eval vm_compute in (FGH omega 0).              (* f_omega(0) = f_0(0) = 1 *)
Eval vm_compute in (FGH omega 1).              (* f_omega(1) = f_1(1) = 2 *)
Eval vm_compute in (FGH omega 2).              (* f_omega(2) = f_2(2) = 8 *)
(* f_omega(3) = f_3(3) is already a number with ~10^8 bits -- way past
   vm_compute's reach.  Definable, just not displayable. *)

(* Hardy at small ordinals: H_omega(n) = 2n,
   H_{omega^2}(n) = 2^n * n. *)
Eval vm_compute in (Hardy omega 5).            (* 10 *)
Eval vm_compute in (Hardy omega 10).           (* 20 *)

(* Bigger ordinals: omega^omega and beyond.  We do NOT vm_compute these at
   large [n] -- the values explode -- but the *terms* type-check. *)
Definition omega_omega : Brouwer := omega_pow omega.

Eval vm_compute in (Hardy omega_omega 0).      (* 0 *)
Eval vm_compute in (Hardy omega_omega 1).      (* H_{omega^omega}(1) *)
Eval vm_compute in (Hardy omega_omega 2).      (* H_{omega^omega}(2) *)

(* omega^^3, omega^^4 are perfectly definable Brouwer terms.  Their
   FGH/Hardy values are too big for vm_compute to print but the kernel
   type-checks them. *)
Definition omega_to_3 : Brouwer := omega_tower 3.   (* omega^omega^omega *)
Definition omega_to_4 : Brouwer := omega_tower 4.

(* -------------------------------------------------------------------- *)
(* Sketch: a "tFGH primitive" contender.                                  *)
(*                                                                       *)
(* Defining [BigGrow := FGH epsilon_0 : nat -> nat] gives us, in Coq,    *)
(* a total function that dominates every primitive-recursive function    *)
(* and in fact every function provably total in Peano arithmetic. *)
(*                                                                       *)
(* Wrap [BigGrow] as a primitive in a new STLC+NatRec+tBigGrow language: *)
(*                                                                       *)
(*   tBigGrow : tpNat -> tpNat                                           *)
(*                                                                       *)
(* interpreted as [BigGrow], and the witness term                        *)
(*                                                                       *)
(*   tApp tBigGrow (natlit 42)                                           *)
(*                                                                       *)
(* evaluates to [BigGrow 42 = FGH epsilon_0 42], a number much larger    *)
(* than [Contender.contender_5 = largest_STLCNatRec_nat_of_depth 42]. *)
(*                                                                       *)
(* The witness [term_depth] is 44 (= 1 + max(1, 43)), where 43 = depth   *)
(* of [natlit 42] (unary).  So the contender                             *)
(*                                                                       *)
(*   contender_BG := largest_BG_nat_of_depth 44                          *)
(*                                                                       *)
(* is mechanically provable larger than [contender_5] using the same     *)
(* maxBy lower-bound proof shape as the reflection-tower sandboxes.       *)
(*                                                                       *)
(* That language wrap-up is left for a follow-up sandbox.                *)
(* -------------------------------------------------------------------- *)

Definition BigGrow (n : nat) : nat := FGH epsilon_0 n.

(* A few small computed values of BigGrow for sanity.  These are tractable
   only because [n] is tiny:

   BigGrow 0 = FGH epsilon_0 0
             = FGH (omega_tower 0) 0
             = FGH one 0
             = FGH (Bsucc Bz) 0
             = Nat.iter 0 (FGH Bz) 0
             = 0.

   BigGrow 1 = FGH epsilon_0 1
             = FGH (omega_tower 1) 1
             = FGH (omega_pow one) 1
             = FGH (Bmul (omega_pow Bz) omega) 1
             = FGH (Bmul one omega) 1.

   We let vm_compute resolve the rest. *)

(* BigGrow 0 = 0 (traceable by hand), BigGrow 1 = 2 (also traceable by hand;
   reduces to FGH (Bsucc Bz) 1 = 2 after a half-dozen Brouwer arithmetic
   steps).  BigGrow 2 already exhausts a sensible vm_compute budget;
   omitting [Eval] here so the file stays in the few-second budget.  All
   four definitions above type-check. *)

Print Assumptions FGH.
Print Assumptions Hardy.
Print Assumptions epsilon_0.
Print Assumptions BigGrow.

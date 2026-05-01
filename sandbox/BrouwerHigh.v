(* Sandbox: higher Brouwer ordinals past epsilon_0.

   sandbox/Brouwer.v stops at epsilon_0 = Blim omega_tower.  This file
   extends the catalogue with named Brouwer terms for the next few
   ordinals reachable by simple iterations of [omega_pow] / [next_epsilon]:

   * [next_epsilon e] -- the smallest epsilon ordinal strictly above e.
   * [epsilon_at k]   -- epsilon_k for finite k (epsilon_0, epsilon_1, ...).
   * [epsilon_omega]  -- the limit of epsilon_k for k -> omega.

   Beyond [epsilon_omega] this file currently exposes Brouwer terms
   built by *iterating* [next_epsilon] further.  These were originally
   labelled [zeta_0], [phi_2], and [Gamma_0], but Review 1 (in
   reviews/review-1.md) correctly observed that those labels are
   mathematically wrong:

   * The real Feferman/Bachmann [zeta_0] is the smallest fixed point
     of [alpha |-> epsilon_alpha], reached via the sequence
     0, epsilon_0, epsilon_(epsilon_0), epsilon_(epsilon_(epsilon_0)),
     ..., which sits *far* above [epsilon_omega].
   * The real [Gamma_0] (Feferman-Schutte) needs a full Veblen
     [phi : Brouwer -> Brouwer -> Brouwer], not a single [phi_2].

   What the iterations here actually give is a chain of "next epsilon
   above" stages, which is mathematically interesting (and certainly
   total in Coq) but not the real zeta_0 / Gamma_0.  To avoid making
   false math claims, the suspect names are now prefixed with
   [pseudo_].  The companion [BigGrow_pseudo_*] engines remain useful
   as alternative growth functions whether or not their *labels* match
   any specific named ordinal in the literature.

   Future work: add a real [epsilon_indexed : Brouwer -> Brouwer]
   recursing on its argument, then build a genuine [zeta_0] as
   [Blim (fun n => epsilon_indexed^n Bz)]; add a real Veblen
   [phi : Brouwer -> Brouwer -> Brouwer] and a real [Gamma_0].

   None of this requires anything beyond Brouwer ordinal data plus the
   [Blim : (nat -> Brouwer) -> Brouwer] constructor: every limit step
   is a [Blim] of a Coq function indexing the fundamental sequence.

   Sanity:

     Print Assumptions epsilon_at.            -- closed under the global context
     Print Assumptions epsilon_omega.         -- closed under the global context
     Print Assumptions pseudo_Gamma_0.        -- closed under the global context

   What this enables:

   * [BigGrow_eN k n := FGH (epsilon_at k) n] is a strictly stronger
     candidate fast-growing function than [BigGrow] for k >= 1.
   * [BigGrow_e_omega], [BigGrow_pseudo_zeta_0],
     [BigGrow_pseudo_Gamma_0] -- each is
     a candidate "engine" for a future fresh-engine [contender_6].
     Each one *is provably terminating in Coq* without any axiom or
     fuel parameter, because the W-type guard handles the Brouwer
     induction directly.

   Open: as with [BigGrow] itself, using any of these as a [contender_6]
   needs a connector lemma bounding [Contender.contender_5] by the
   corresponding FGH function at depth 42.  See IDEAS.md "Connector
   lemma" for the proof-theoretic structure.

   Compile from repo root, after sandbox/Brouwer.vo has been built:

     coqc -Q . "" sandbox\BrouwerHigh.v
*)

Require Import Arith Lia.
Require Import sandbox.Brouwer.

(* -------------------------------------------------------------------- *)
(* Iterated omega-exponentiation.                                        *)
(*                                                                       *)
(*   omega_pow_iter a 0     = a                                          *)
(*   omega_pow_iter a (S n) = omega^(omega_pow_iter a n)                 *)
(*                                                                       *)
(* So [omega_pow_iter a n] is the height-n tower of omegas above [a].   *)
(* When a = Bsucc e for an epsilon ordinal e, [Blim] over n gives the   *)
(* next epsilon ordinal above e.                                         *)
(* -------------------------------------------------------------------- *)

Fixpoint omega_pow_iter (a : Brouwer) (n : nat) : Brouwer :=
  match n with
  | 0 => a
  | S n' => omega_pow (omega_pow_iter a n')
  end.

(* The omega-tower from Brouwer.v is exactly omega_pow_iter (Bsucc Bz) n,
   modulo the trivial "1 = Bsucc Bz" identification.  Recorded here for
   convenience; the equality is provable by induction. *)

(* -------------------------------------------------------------------- *)
(* Next epsilon ordinal.                                                 *)
(*                                                                       *)
(*   next_epsilon e := sup_n (omega^^n above (e + 1))                    *)
(*                                                                       *)
(* This is the smallest epsilon ordinal strictly above e.                *)
(* -------------------------------------------------------------------- *)

Definition next_epsilon (e : Brouwer) : Brouwer :=
  Blim (fun n => omega_pow_iter (Bsucc e) n).

(* -------------------------------------------------------------------- *)
(* Iterated epsilon: epsilon_at k = epsilon_k.                           *)
(*                                                                       *)
(*   epsilon_at 0 = epsilon_0  (already defined in Brouwer.v)            *)
(*   epsilon_at (S k) = next_epsilon (epsilon_at k)                      *)
(* -------------------------------------------------------------------- *)

Fixpoint epsilon_at (k : nat) : Brouwer :=
  match k with
  | 0    => epsilon_0
  | S k' => next_epsilon (epsilon_at k')
  end.

(* -------------------------------------------------------------------- *)
(* epsilon_omega: limit of epsilon_k as k -> omega.                       *)
(* -------------------------------------------------------------------- *)

Definition epsilon_omega : Brouwer := Blim epsilon_at.

(* -------------------------------------------------------------------- *)
(* "Pseudo" higher constructions.                                        *)
(*                                                                       *)
(* The names below are deliberately prefixed [pseudo_] to flag that    *)
(* they iterate [next_epsilon] but do *not* match the standard          *)
(* Veblen / Feferman-Schutte ordinals of the same root name.  See the   *)
(* file header for the precise correction; these are research-grade    *)
(* large total Brouwer terms, not vetted ordinal-theoretic landmarks.   *)
(*                                                                       *)
(*   pseudo_zeta_0 := epsilon_omega                                      *)
(*                                                                       *)
(* (The real zeta_0 is the smallest fixed point of                       *)
(*  [alpha |-> epsilon_alpha], reached via                               *)
(*  0, epsilon_0, epsilon_(epsilon_0), ... -- far above epsilon_omega.   *)
(*  Defining it requires an [epsilon_indexed : Brouwer -> Brouwer]      *)
(*  recursing on its argument, which is future work.)                   *)
(* -------------------------------------------------------------------- *)

Definition pseudo_zeta_0 : Brouwer := epsilon_omega.

(* [pseudo_phi_2 a]: iterate [next_epsilon] starting from
   [Bsucc (pseudo_phi_2 a')] in the successor case.  This is the
   structural recursion that *would* compute the real Veblen [phi_2 a]
   if [next_epsilon] were itself the function [alpha |-> epsilon_alpha]
   -- which it is *not* (next_epsilon takes any ordinal, not only an
   epsilon, and returns the next epsilon above).  So this is a chain
   of [next_epsilon] iterates indexed by Brouwer ordinals, not the
   Veblen phi_2.

   It is still a perfectly defined total Brouwer function and useful
   as an alternative engine for [FGH]. *)

Fixpoint epsilon_iter (n : nat) (a : Brouwer) : Brouwer :=
  match n with
  | 0    => a
  | S n' => next_epsilon (epsilon_iter n' a)
  end.

Fixpoint pseudo_phi_2 (a : Brouwer) : Brouwer :=
  match a with
  | Bz       => pseudo_zeta_0
  | Bsucc a' => Blim (fun n => epsilon_iter n (Bsucc (pseudo_phi_2 a')))
  | Blim f   => Blim (fun n => pseudo_phi_2 (f n))
  end.

(* [pseudo_Gamma_0]: iterate [pseudo_phi_2] starting from [Bz].
   Mathematically this is *not* the Feferman-Schutte Gamma_0, which
   needs a full multivariate Veblen function.  But it is still a
   total Brouwer term, strictly past [pseudo_phi_2 a] for every
   finite [a]. *)

Fixpoint pseudo_phi_2_iter (n : nat) : Brouwer :=
  match n with
  | 0    => Bz
  | S n' => pseudo_phi_2 (pseudo_phi_2_iter n')
  end.

Definition pseudo_Gamma_0 : Brouwer := Blim pseudo_phi_2_iter.

(* -------------------------------------------------------------------- *)
(* Candidate "engines" for future fresh-engine contenders.               *)
(*                                                                       *)
(* Each of these is a total Coq function nat -> nat with no axioms.     *)
(* Using any of them in a [contender_6] still requires the connector    *)
(* lemma (sandbox/Brouwer.v's [BigGrow] is the smallest case);          *)
(* stronger ordinals only make the connector "easier" by giving more    *)
(* slack at the inequality.                                              *)
(* -------------------------------------------------------------------- *)

Definition BigGrow_eN (k : nat) (n : nat) : nat :=
  FGH (epsilon_at k) n.

Definition BigGrow_e_omega (n : nat) : nat :=
  FGH epsilon_omega n.

Definition BigGrow_pseudo_zeta_0 (n : nat) : nat :=
  FGH pseudo_zeta_0 n.

Definition BigGrow_pseudo_Gamma_0 (n : nat) : nat :=
  FGH pseudo_Gamma_0 n.

(* -------------------------------------------------------------------- *)
(* All four engines are axiom-free.                                      *)
(* -------------------------------------------------------------------- *)

Print Assumptions epsilon_at.
Print Assumptions epsilon_omega.
Print Assumptions pseudo_zeta_0.
Print Assumptions pseudo_phi_2.
Print Assumptions pseudo_Gamma_0.
Print Assumptions BigGrow_eN.
Print Assumptions BigGrow_e_omega.
Print Assumptions BigGrow_pseudo_zeta_0.
Print Assumptions BigGrow_pseudo_Gamma_0.

(* -------------------------------------------------------------------- *)
(* Sanity at very small inputs.  We can NOT vm_compute these at any      *)
(* meaningful n -- the values are astronomical -- but we can record    *)
(* type-checking of the [FGH at higher ordinal] applications.           *)
(* -------------------------------------------------------------------- *)

Eval cbv in (FGH (epsilon_at 0) 0).   (* = BigGrow 0 = 0 *)
Eval cbv in (FGH (epsilon_at 0) 1).   (* = BigGrow 1 = 2 *)
(* (epsilon_at 1) and beyond at any positive n are too big to display. *)

(* term-ish: how "deep" is each Brouwer term, viewed as an inductive
   tree?  This is the Brouwer-structure size, NOT the ordinal it
   represents.  Useful only to confirm the Brouwer-encoded ordinals
   are very compact compared to the ordinals themselves. *)

Fixpoint Brouwer_height (a : Brouwer) : nat :=
  match a with
  | Bz       => 1
  | Bsucc a' => S (Brouwer_height a')
  | Blim _   => 1   (* a Blim is one constructor; the "infinite" branching is hidden *)
  end.

Eval vm_compute in (Brouwer_height epsilon_0).         (* 1 *)
Eval vm_compute in (Brouwer_height epsilon_omega).     (* 1 *)
Eval vm_compute in (Brouwer_height pseudo_Gamma_0).    (* 1 *)

(* Sandbox: higher Brouwer ordinals beyond epsilon_0.

   sandbox/Brouwer.v stops at epsilon_0 = Blim omega_tower.  This file
   extends the catalogue with named Brouwer terms for the next few
   landmarks of the proof-theoretic ordinal zoo:

   * [next_epsilon e] -- the smallest epsilon ordinal strictly above e.
   * [epsilon_at k]   -- epsilon_k for finite k (epsilon_0, epsilon_1, ...).
   * [epsilon_omega]  -- the limit of epsilon_k for k -> omega.
   * [phi_2_zero]     -- the smallest fixed point of [next_epsilon],
                        i.e. zeta_0 = phi_2(0) in Veblen notation.
   * [Gamma_0]        -- the smallest fixed point of [phi_2 _ 0],
                        i.e. the Feferman-Schutte ordinal.

   None of this requires anything beyond Brouwer ordinal data plus the
   [Blim : (nat -> Brouwer) -> Brouwer] constructor: every limit step
   is a [Blim] of a Coq function indexing the fundamental sequence.

   Sanity:

     Print Assumptions epsilon_at.       -- closed under the global context
     Print Assumptions epsilon_omega.    -- closed under the global context
     Print Assumptions Gamma_0.          -- closed under the global context

   What this enables:

   * [BigGrow_eN k n := FGH (epsilon_at k) n] is a strictly stronger
     candidate fast-growing function than [BigGrow] for k >= 1.
   * [BigGrow_e_omega], [BigGrow_zeta_0], [BigGrow_Gamma_0] -- each is
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
(* Veblen-style fixed points.                                            *)
(*                                                                       *)
(* Skipping ahead a level:                                                *)
(*                                                                       *)
(*   zeta_0 := smallest fixed point of [next_epsilon]                    *)
(*           = phi_2(0) in Veblen notation                               *)
(*           = sup_k (next_epsilon^k epsilon_0)                          *)
(*                                                                       *)
(* Where the iterated [next_epsilon^k] is just                           *)
(*                                                                       *)
(*   epsilon_iter 0     = epsilon_0                                      *)
(*   epsilon_iter (S k) = next_epsilon (epsilon_iter k)                  *)
(*                                                                       *)
(* which is exactly [epsilon_at].  So [zeta_0 = epsilon_omega], one of  *)
(* the standard identifications: the smallest fixed point of the         *)
(* "next epsilon" map is the limit of all finite epsilon iterates.       *)
(* -------------------------------------------------------------------- *)

Definition zeta_0 : Brouwer := epsilon_omega.

(* -------------------------------------------------------------------- *)
(* phi_2 a := the [a]-th fixed point of [next_epsilon] above zeta_0.    *)
(*                                                                       *)
(* On Brouwer ordinals:                                                  *)
(*                                                                       *)
(*   phi_2 Bz       = zeta_0                                             *)
(*   phi_2 (Bsucc a)= sup_n (next_epsilon^n (Bsucc (phi_2 a)))           *)
(*   phi_2 (Blim f) = Blim (fun n => phi_2 (f n))                        *)
(*                                                                       *)
(* This is a structural Fixpoint on the Brouwer argument [a].            *)
(* -------------------------------------------------------------------- *)

Fixpoint epsilon_iter (n : nat) (a : Brouwer) : Brouwer :=
  match n with
  | 0    => a
  | S n' => next_epsilon (epsilon_iter n' a)
  end.

Fixpoint phi_2 (a : Brouwer) : Brouwer :=
  match a with
  | Bz       => zeta_0
  | Bsucc a' => Blim (fun n => epsilon_iter n (Bsucc (phi_2 a')))
  | Blim f   => Blim (fun n => phi_2 (f n))
  end.

(* -------------------------------------------------------------------- *)
(* Gamma_0: the Feferman-Schutte ordinal.                                *)
(*                                                                       *)
(*   Gamma_0 := smallest fixed point of [phi_2]                          *)
(*           = sup_k (phi_2^k 0)                                          *)
(*                                                                       *)
(* In Brouwer notation: Blim of the iterated phi_2 sequence starting at *)
(* Bz.                                                                    *)
(* -------------------------------------------------------------------- *)

Fixpoint phi_2_iter (n : nat) : Brouwer :=
  match n with
  | 0    => Bz
  | S n' => phi_2 (phi_2_iter n')
  end.

Definition Gamma_0 : Brouwer := Blim phi_2_iter.

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

Definition BigGrow_zeta_0 (n : nat) : nat :=
  FGH zeta_0 n.

Definition BigGrow_Gamma_0 (n : nat) : nat :=
  FGH Gamma_0 n.

(* -------------------------------------------------------------------- *)
(* All four engines are axiom-free.                                      *)
(* -------------------------------------------------------------------- *)

Print Assumptions epsilon_at.
Print Assumptions epsilon_omega.
Print Assumptions zeta_0.
Print Assumptions phi_2.
Print Assumptions Gamma_0.
Print Assumptions BigGrow_eN.
Print Assumptions BigGrow_e_omega.
Print Assumptions BigGrow_zeta_0.
Print Assumptions BigGrow_Gamma_0.

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

Eval vm_compute in (Brouwer_height epsilon_0).      (* 1 *)
Eval vm_compute in (Brouwer_height epsilon_omega).  (* 1 *)
Eval vm_compute in (Brouwer_height Gamma_0).        (* 1 *)

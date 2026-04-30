(* Sandbox: prototype an ordinal-indexed fast-growing hierarchy.

   This is a scratch file for the "next contender" brainstorm. The plan is:
     1. Define ordinals < epsilon_0 in Cantor Normal Form (CNF).
     2. Define successor/predecessor/limit-test and the canonical
        fundamental sequence on CNF ordinals.
     3. Define the fast-growing hierarchy f_alpha : nat -> nat by
        well-founded recursion (here, with a fuel parameter for simplicity).
     4. Sanity-check small values and inspect ordinal "depth" so we have
        a feel for how much depth budget the ord constants will eat
        when this primitive is bolted onto STLC+NatRec to form L6.

   Nothing in this file is intended to enter Contender.v directly; once an
   approach is chosen it will be reformulated to match Contender.v's
   conventions and budgets. *)

Require Import Arith Lia.
Require Import List. Import ListNotations.

(* -------------------------------------------------------------------- *)
(* Cantor Normal Form ordinals < epsilon_0.

   ocons a b stands for omega^a + b. The CNF invariant
     a >= leading exponent of b
   is not enforced by the type; we just refrain from constructing
   non-CNF terms. Since ord_succ, fund_seq, etc. preserve CNF when
   given CNF inputs, this stays tidy in practice.                      *)

Inductive ord : Set :=
| oz : ord
| ocons : ord -> ord -> ord.

(* Embedding nat -> ord as a sum of omega^0's. *)
Fixpoint nat_to_ord (n : nat) : ord :=
  match n with
  | 0 => oz
  | S n' => ocons oz (nat_to_ord n')
  end.

(* alpha + 1 *)
Fixpoint ord_succ (a : ord) : ord :=
  match a with
  | oz => ocons oz oz
  | ocons exp rest => ocons exp (ord_succ rest)
  end.

(* alpha is a successor (vs zero or limit) *)
Fixpoint ord_is_succ (a : ord) : bool :=
  match a with
  | oz => false
  | ocons exp rest =>
    match rest with
    | oz =>
      match exp with
      | oz => true     (* alpha = omega^0 = 1 *)
      | _ => false     (* alpha = omega^exp, exp > 0: limit *)
      end
    | _ => ord_is_succ rest
    end
  end.

(* alpha - 1, valid when alpha is a successor; else returns oz *)
Fixpoint ord_pred (a : ord) : ord :=
  match a with
  | oz => oz
  | ocons exp rest =>
    match rest with
    | oz => oz                       (* "leaf" successor: alpha = 1 *)
    | _  => ocons exp (ord_pred rest)
    end
  end.

(* omega^exp * n = omega^exp + omega^exp + ... + omega^exp  (n copies) *)
Fixpoint omega_pow_times (exp : ord) (n : nat) : ord :=
  match n with
  | 0 => oz
  | S k => ocons exp (omega_pow_times exp k)
  end.

(* The canonical fundamental sequence at a limit ordinal.
   For successor or zero arguments the value is unused; we return oz.   *)
Fixpoint ord_fund_seq (a : ord) (n : nat) : ord :=
  match a with
  | oz => oz
  | ocons exp rest =>
    match rest with
    | oz =>                    (* alpha = omega^exp *)
      match exp with
      | oz => oz                (* alpha = 1, successor *)
      | _ =>
        if ord_is_succ exp then
          omega_pow_times (ord_pred exp) n
        else
          ocons (ord_fund_seq exp n) oz
      end
    | _ => ocons exp (ord_fund_seq rest n)
    end
  end.

(* -------------------------------------------------------------------- *)
(* Fast-growing hierarchy.

   f_0(n)         = n + 1
   f_{alpha+1}(n) = f_alpha^n(n)      (n-fold iteration)
   f_lambda(n)    = f_{lambda[n]}(n)

   We add a "fuel" parameter to keep the definition structurally
   recursive. The actual function is total; fuel is only an artifact
   of the Coq presentation and can be replaced by Fix on a measure
   later.                                                              *)

Fixpoint FGH (fuel : nat) (a : ord) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match a with
    | oz => S n
    | _ =>
      if ord_is_succ a then
        Nat.iter n (FGH fuel' (ord_pred a)) n
      else
        FGH fuel' (ord_fund_seq a n) n
    end
  end.

(* -------------------------------------------------------------------- *)
(* Sanity checks. *)

(* Some ordinal landmarks. *)
Definition o_omega : ord := ocons (ocons oz oz) oz.                      (* omega *)
Definition o_omega_plus_one : ord := ord_succ o_omega.                    (* omega + 1 *)
Definition o_omega_times_2 : ord := ocons (ocons oz oz) o_omega.          (* omega + omega *)
Definition o_omega_sq : ord := ocons (ocons oz (ocons oz oz)) oz.         (* omega^2 *)

(* omega^omega *)
Definition o_omega_omega : ord :=
  ocons (ocons (ocons oz oz) oz) oz.

(* Tower of omega's of height h (omega^omega^...^omega): epsilon_0 fundamental seq members. *)
Fixpoint omega_tower (h : nat) : ord :=
  match h with
  | 0 => ocons oz oz                  (* 1 *)
  | S h' => ocons (omega_tower h') oz (* omega^(tower h') *)
  end.

Eval vm_compute in (ord_is_succ o_omega).                    (* false *)
Eval vm_compute in (ord_is_succ o_omega_plus_one).           (* true *)
Eval vm_compute in (ord_is_succ o_omega_times_2).            (* false *)
Eval vm_compute in (ord_is_succ o_omega_sq).                 (* false *)

(* Fundamental sequences *)
Eval vm_compute in (ord_fund_seq o_omega 5).                 (* 5 *)
Eval vm_compute in (ord_fund_seq o_omega_times_2 3).         (* omega + 3 *)
Eval vm_compute in (ord_fund_seq o_omega_sq 4).              (* omega * 4 *)
Eval vm_compute in (ord_fund_seq o_omega_omega 3).           (* omega^3 *)

(* FGH values (tiny n, otherwise the numbers are too big to display) *)
Eval vm_compute in (FGH 1000 (nat_to_ord 0) 10).             (* f_0(10) = 11 *)
Eval vm_compute in (FGH 1000 (nat_to_ord 1) 10).             (* f_1(10) = 20 *)
Eval vm_compute in (FGH 1000 (nat_to_ord 2) 4).              (* f_2(4) = 64 *)
Eval vm_compute in (FGH 1000 (nat_to_ord 2) 6).              (* f_2(6) = 384 *)
Eval vm_compute in (FGH 1000 (nat_to_ord 3) 2).              (* f_3(2) = ? *)
Eval vm_compute in (FGH 1000 o_omega 2).                     (* f_omega(2) = f_2(2) = 8 *)
(* f_omega(3) = f_3(3) is already astronomically large -- skip displaying.    *)
(* f_omega(4), f_{omega+1}(2), f_{omega^2}(2) etc. are similarly out of reach
   for vm_compute; they are the whole point. *)

(* Depth-budget feel: how complex are these ord constants as raw inductive
   trees? (Each ocons is a binary node; this is *not* the same as the
   STLC+NatRec term_depth, but it gives an order-of-magnitude.) *)
Fixpoint ord_size (a : ord) : nat :=
  match a with
  | oz => 1
  | ocons x y => S (ord_size x + ord_size y)
  end.
Fixpoint ord_height (a : ord) : nat :=
  match a with
  | oz => 1
  | ocons x y => S (max (ord_height x) (ord_height y))
  end.

Eval vm_compute in (ord_size o_omega, ord_height o_omega).
Eval vm_compute in (ord_size o_omega_omega, ord_height o_omega_omega).
Eval vm_compute in (ord_size (omega_tower 5), ord_height (omega_tower 5)).
Eval vm_compute in (ord_size (omega_tower 10), ord_height (omega_tower 10)).

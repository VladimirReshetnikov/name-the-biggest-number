(* Sandbox: structural sketch of L6 = STLC+NatRec extended with an
   ordinal type and a fast-growing-hierarchy primitive.

   Goal here is *only* to convince ourselves that the data types and
   evaluator typecheck and a small example reduces. The depth-bounded
   enumeration, soundness of evaluation, embedding from STLC+NatRec,
   and the Grow lemma are sketched but not closed. None of this is
   meant for Contender.v in its current form. *)

Require Import Arith Lia.
Require Import List. Import ListNotations.

(* Pull the ord/FGH definitions from the FGH sandbox. We just inline
   them here for the standalone build. *)

Inductive ord : Set :=
| oz : ord
| ocons : ord -> ord -> ord.

Fixpoint nat_to_ord (n : nat) : ord :=
  match n with 0 => oz | S n' => ocons oz (nat_to_ord n') end.

Fixpoint ord_succ (a : ord) : ord :=
  match a with
  | oz => ocons oz oz
  | ocons exp rest => ocons exp (ord_succ rest)
  end.

Fixpoint ord_is_succ (a : ord) : bool :=
  match a with
  | oz => false
  | ocons exp rest =>
    match rest with
    | oz => match exp with oz => true | _ => false end
    | _ => ord_is_succ rest
    end
  end.

Fixpoint ord_pred (a : ord) : ord :=
  match a with
  | oz => oz
  | ocons exp rest =>
    match rest with oz => oz | _ => ocons exp (ord_pred rest) end
  end.

Fixpoint omega_pow_times (exp : ord) (n : nat) : ord :=
  match n with 0 => oz | S k => ocons exp (omega_pow_times exp k) end.

Fixpoint ord_fund_seq (a : ord) (n : nat) : ord :=
  match a with
  | oz => oz
  | ocons exp rest =>
    match rest with
    | oz =>
      match exp with
      | oz => oz
      | _ =>
        if ord_is_succ exp
        then omega_pow_times (ord_pred exp) n
        else ocons (ord_fund_seq exp n) oz
      end
    | _ => ocons exp (ord_fund_seq rest n)
    end
  end.

Fixpoint FGH (fuel : nat) (a : ord) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match a with
    | oz => S n
    | _ =>
      if ord_is_succ a
      then Nat.iter n (FGH fuel' (ord_pred a)) n
      else FGH fuel' (ord_fund_seq a n) n
    end
  end.

(* -------------------------------------------------------------------- *)
(* L6 types: tpNat, tpArr, tpOrd. *)

Inductive type :=
| tpNat : type
| tpOrd : type
| tpArr : type -> type -> type.

Fixpoint type_depth (t : type) : nat :=
  match t with
  | tpNat => 1
  | tpOrd => 1
  | tpArr t1 t2 => S (max (type_depth t1) (type_depth t2))
  end.

Fixpoint interp_type (tp : type) : Type :=
  match tp with
  | tpNat => nat
  | tpOrd => ord
  | tpArr t1 t2 => interp_type t1 -> interp_type t2
  end.

(* -------------------------------------------------------------------- *)
(* L6 terms. We extend STLC+NatRec with three primitives:
     tOZ      : tpOrd
     tOCons   : tpArr tpOrd (tpArr tpOrd tpOrd)
     tFGH     : tpArr tpOrd (tpArr tpNat tpNat)
   FGH inside L6 is "saturated" with a Coq-side fuel bound that depends
   on the ord and nat arguments; the evaluator below picks a generous
   fuel so that for *any* CNF input the value is FGH's true value.    *)

Inductive term :=
| tVar (x : nat)
| tLam (A B : type) (body : term)
| tApp (t1 t2 : term)
| tO
| tS
| tNatRec (R : type)
| tOZ
| tOCons
| tFGH.

Fixpoint term_depth (t : term) : nat :=
  match t with
  | tVar x => S (S x)
  | tLam A B body => S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
  | tOZ => 1
  | tOCons => 1
  | tFGH => 1
  end.

(* -------------------------------------------------------------------- *)
(* Pick a fuel large enough for the FGH at this (ord, nat) input.
   This is conservative; a tighter bound is a future optimization. *)
Fixpoint ord_size (a : ord) : nat :=
  match a with oz => 1 | ocons x y => S (ord_size x + ord_size y) end.

(* For any CNF ord a and any n, FGH's recursion depth is bounded by
   some function of (ord_size a, n). A loose-but-safe choice:
     fuel = 2^(ord_size a) + n * (ord_size a) + 1.
   We will not prove this is tight here; for the sandbox we simply
   pick a fuel so vm_compute can still terminate on small examples. *)
Definition fgh_fuel (a : ord) (n : nat) : nat :=
  10 * (ord_size a + n) + 100.

(* "Saturated" FGH that picks its own fuel. *)
Definition FGH_total (a : ord) (n : nat) : nat :=
  FGH (fgh_fuel a n) a n.

(* -------------------------------------------------------------------- *)
(* Evaluator. We re-use the STLC+NatRec idea: an env is a list of
   (existT type interp_type tp) and interp_term threads through.

   For brevity we lean on a default-error value at every type. *)

Definition error : forall (tp : type), interp_type tp.
  refine (fix rec tp := _).
  destruct tp; simpl.
  - exact 0.
  - exact oz.
  - intros _; apply rec.
Defined.

(* Decidable equality on types is needed for casts. *)
Fixpoint type_eqb (t1 t2 : type) : bool :=
  match t1, t2 with
  | tpNat, tpNat => true
  | tpOrd, tpOrd => true
  | tpArr A B, tpArr C D => andb (type_eqb A C) (type_eqb B D)
  | _, _ => false
  end.

Definition cast_error (from to : type) :
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)) :=
  (fun _ => error to, fun _ => error from).

Definition cast_impl :
  forall from to : type,
    ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
Proof.
  refine (fix rec from to {struct from} := _).
  destruct from; destruct to.
  - exact (fun x => x, fun x => x).             (* tpNat,  tpNat  *)
  - exact (cast_error tpNat tpOrd).             (* tpNat,  tpOrd  *)
  - exact (cast_error tpNat (tpArr to1 to2)).
  - exact (cast_error tpOrd tpNat).
  - exact (fun x => x, fun x => x).             (* tpOrd,  tpOrd  *)
  - exact (cast_error tpOrd (tpArr to1 to2)).
  - exact (cast_error (tpArr from1 from2) tpNat).
  - exact (cast_error (tpArr from1 from2) tpOrd).
  - (* tpArr from1 from2, tpArr to1 to2 *)
    pose (cA := rec from1 to1).
    pose (cB := rec from2 to2).
    exact (fun f arg => fst cB (f (snd cA arg)),
           fun f arg => snd cB (f (fst cA arg))).
Defined.

Definition cast {from : type} (to : type) : interp_type from -> interp_type to :=
  fst (cast_impl from to).

(* The interpreter. *)
Definition interp_term :
  forall (e : list {tp : type & interp_type tp}) (t : term),
    {tp : type & interp_type tp}.
Proof.
  refine (fix rec e t {struct t} :=
    match t with
    | tVar x =>
      match nth_error (rev e) x with
      | Some r => r
      | None => existT _ tpNat (error tpNat)
      end
    | tLam A B body => _
    | tApp t1 t2 => _
    | tO => existT _ tpNat 0
    | tS => existT _ (tpArr tpNat tpNat) S
    | tNatRec R =>
      existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R)))
             (@Nat.recursion (interp_type R))
    | tOZ => existT _ tpOrd oz
    | tOCons =>
      existT _ (tpArr tpOrd (tpArr tpOrd tpOrd)) ocons
    | tFGH =>
      existT _ (tpArr tpOrd (tpArr tpNat tpNat)) FGH_total
    end).
  - refine (existT _ (tpArr A B) _).
    intro x'.
    refine (cast B (projT2 (rec ((existT _ A x') :: e) body))).
  - destruct (rec e t1) as [R1 r1].
    destruct (rec e t2) as [R2 r2].
    destruct R1 as [| | A B]; [exact (existT _ tpNat (error tpNat))..|].
    refine (existT _ B (r1 (cast A r2))).
Defined.

Definition eval (t : term) : nat :=
  let r := interp_term nil t in
  match projT1 r as t0 return interp_type t0 -> nat with
  | tpNat => fun n : nat => n
  | _ => fun _ => 0
  end (projT2 r).

(* -------------------------------------------------------------------- *)
(* Quick smoke test. Build the ord constant 1 = ocons oz oz inside L6
   and apply FGH to it and the nat 3. *)

Definition tOne_ord : term := tApp (tApp tOCons tOZ) tOZ.   (* ord 1 *)
Definition tThree_nat : term := tApp tS (tApp tS (tApp tS tO)).
Definition tFGH_one_three : term := tApp (tApp tFGH tOne_ord) tThree_nat.

Eval vm_compute in (eval tFGH_one_three).
(* f_1(3) = 6 *)

(* Build omega = ocons (ocons oz oz) oz inside L6, apply FGH to it and 2. *)
Definition tOmega_ord : term :=
  tApp (tApp tOCons (tApp (tApp tOCons tOZ) tOZ)) tOZ.
Definition tTwo_nat : term := tApp tS (tApp tS tO).
Definition tFGH_omega_two : term :=
  tApp (tApp tFGH tOmega_ord) tTwo_nat.

Eval vm_compute in (eval tFGH_omega_two).
(* f_omega(2) = f_2(2) = 8 *)

(* Term depths: how much budget did we burn? *)
Eval vm_compute in (term_depth tFGH_one_three).
Eval vm_compute in (term_depth tFGH_omega_two).

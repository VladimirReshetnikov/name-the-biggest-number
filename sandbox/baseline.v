(* Sandbox: probe baseline values of the current STLC+NatRec contender at
   tiny depths. Throwaway file; not intended to enter Contender.v.

   Compile (from repo root, after Contender.v has been built):
     coqc -Q . "" sandbox/baseline.v
   or, from inside sandbox/:
     coqc -Q .. "" baseline.v *)

Require Import Arith Lia.
Require Import List. Import ListNotations.

From Stdlib Require Import Logic.
Require Contender.
Import Contender.

Eval vm_compute in (List.length (termsUpTo 1)).
Eval vm_compute in (List.length (termsUpTo 2)).
Eval vm_compute in (List.length (termsUpTo 3)).
Eval vm_compute in (List.length (termsUpTo 4)).

Eval vm_compute in (largest_STLCNatRec_nat_of_depth 1).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 2).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 3).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 4).

(* Depths used by the contender witnesses: *)
Eval vm_compute in (term_depth ack_reified).
Eval vm_compute in (term_depth contender_4''_reified).

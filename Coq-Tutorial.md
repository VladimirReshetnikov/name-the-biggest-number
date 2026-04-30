# The Coq Proof Assistant — Tutorial (notes)

> **Source.** Gérard Huet, Gilles Kahn, Christine Paulin-Mohring,
> *The Coq Proof Assistant — A Tutorial*, version 8.4pl3,
> December 16, 2013. © INRIA 1999–2004 (Coq 7.x), © INRIA 2004–2012
> (Coq 8.x). Distributed with the Coq system; canonical copy at
> <https://coq.inria.fr/distrib/current/files/Tutorial.pdf>.
>
> **What this file is.** A structured summary of the tutorial in our
> own words, with brief illustrative tactic snippets and section page
> hooks, so we can navigate to the right part of the PDF quickly while
> brainstorming. It is *not* a verbatim conversion — for the full text
> read [Coq Tutorial.pdf](Coq%20Tutorial.pdf).
>
> **Caveat.** The tutorial targets Coq 8.4. Most of it still works on
> Rocq 9 with deprecation warnings; a few command names changed
> (e.g. `Hint Resolve` is now `#[export] Hint Resolve`, library
> reimport syntax has shifted to `From Stdlib Require ...`).

## Table of contents

- [Front matter](#front-matter)
- [Chapter 1 — Basic Predicate Calculus](#chapter-1--basic-predicate-calculus)
  - [1.1 Gallina overview](#11-gallina-overview)
  - [1.2 The proof engine: minimal logic](#12-the-proof-engine-minimal-logic)
  - [1.3 Propositional calculus](#13-propositional-calculus)
  - [1.4 Predicate calculus](#14-predicate-calculus)
  - [1.5 Using definitions](#15-using-definitions)
- [Chapter 2 — Induction](#chapter-2--induction)
  - [2.1 Inductive types](#21-inductive-types)
  - [2.2 Logic programming with `auto`](#22-logic-programming-with-auto)
- [Chapter 3 — Modules](#chapter-3--modules)
- [Pointers for further reading](#pointers-for-further-reading)

---

## Front matter

The tutorial introduces Coq as a proof assistant for the Calculus of
Inductive Constructions. Scope: the basic specification language
(Gallina) and the main proof tactics; *not* a comprehensive treatment.
Readers are pointed at the Coq Reference Manual and Bertot &
Castéran's *Coq'Art* for depth.

The session model used throughout: lines starting with `Coq <` are
user input (terminated by a period); lines that follow are Coq's
response. CoqIde is the recommended GUI, but the tutorial works in a
plain shell.

## Chapter 1 — Basic Predicate Calculus

### 1.1 Gallina overview

Three sorts: `Prop` (propositions), `Set` (mathematical
collections / data), `Type` (the abstract type universe). Every
expression `e` has a type `E`, written `e : E`, and `Check e` reports
that type. `O : nat`, `nat : Set`, `nat -> Prop : Type`.

Sections (`Section Foo. ... End Foo.`) bound the scope of local
parameters and hypotheses; `Reset Foo` discards a section's contents.

**Declarations** (1.1.1) introduce names with specifications:

```coq
Variable n : nat.            (* "let n be a natural number"  *)
Hypothesis Pos_n : (gt n 0). (* "...and assume n > 0"        *)
```

**Definitions** (1.1.2) link a name to a value, optionally with a
type ascription. Functions are introduced by abstraction
(`fun x:A => e`) or by parameter lists in `Definition`:

```coq
Definition double (m : nat) := plus m m.
```

Universal quantification uses `forall x:A, P`, paralleling functional
abstraction at the type level.

### 1.2 The proof engine: minimal logic

Section pp. 8–11. Introduces the interactive proof loop.

`Goal P.` enters proof mode; the system displays the current goal
under a horizontal line, with local hypotheses above it. Tactics
manipulate goals. The "minimal logic" tactics covered:

- `intro H` / `intros H1 H2 ...` — move antecedent(s) of an
  implication into hypotheses.
- `apply H` — use `H : A1 -> ... -> An -> C` to reduce a goal `C`
  to the subgoals `A1, ..., An`.
- `exact H` — close the goal when `H` already has its exact type.
- `assumption` — search the context for a matching hypothesis.

Demonstrated on the small tautology
`(A -> B -> C) -> (A -> B) -> A -> C`. Closing with `Qed.` checks the
proof and saves it; `Defined.` does the same but keeps the term
reducible (matters for computation, not for ordinary lemmas).

### 1.3 Propositional calculus

#### 1.3.1 Conjunction

`A /\ B` (`and A B`) introduced via `split` (one goal per
conjunct) and eliminated via `destruct H as [HA HB]` (or the older
`elim H; intros HA HB`). The tactic `assumption` typically discharges
the resulting subgoals.

#### 1.3.2 Disjunction

`A \/ B` (`or A B`). To prove a disjunction, pick a side with `left`
or `right`. To use one, case-split with `destruct H as [HA | HB]`.

#### 1.3.3 Tauto

`tauto` is a decision procedure for intuitionistic propositional
logic. It closes any tautology in `A`, `B`, `C`, ... built from
`/\`, `\/`, `->`, `~`, `True`, `False`. It does *not* know classical
laws like the law of excluded middle.

#### 1.3.4 Classical reasoning

For excluded middle and friends, `Require Import Classical.` adds
the axiom `classic : forall P, P \/ ~P`. Tactics like
`destruct (classic P)` then enable case-splits on undecided
propositions. Paired tactics `intuition`, `firstorder`, and
`classical_left`/`classical_right` automate combinations.

### 1.4 Predicate calculus

#### 1.4.1 Sections and signatures

Sections also act as *signatures*: variables and hypotheses
introduced inside a section become universally-quantified parameters
of every definition that mentions them, after the section closes.
This is how Coq replaces the OCaml-style "module signature" idiom for
small developments.

#### 1.4.2 Existential quantification

`exists x, P x` is the type former. Introduce with `exists witness;
...`. Eliminate with `destruct H as [w Hw]` (older: `elim H; intros w
Hw`). The witness can depend on hypothesis context, which is the
whole point.

#### 1.4.3 Paradoxes of classical predicate calculus

A worked example showing how excluded middle plus a quantifier
flip can derive surprising statements (the "drinker's paradox"
genre). Useful pedagogically as a stress test of the `classic`
axiom.

#### 1.4.4 Flexible use of local assumptions

Tactics for renaming, generalising, and clearing local hypotheses:
`rename H1 into H2`, `generalize`, `clear`, `revert`. Used to keep
the context tidy and to set up induction at the right level.

#### 1.4.5 Equality

`a = b` is Leibniz equality on the appropriate type. Tactics:
`reflexivity`, `symmetry`, `transitivity middle`, `rewrite H` (and
`rewrite <- H`), `subst x`. The induction-on-equality lemma is
`eq_ind`; most users never invoke it directly.

### 1.5 Using definitions

#### 1.5.1 Unfolding definitions

`unfold f` replaces `f` with its body inside the goal (or a
hypothesis with `unfold f in H`). Useful when an automated tactic
gets stuck because it cannot see through a `Definition`.

#### 1.5.2 Principle of proof irrelevance

For propositions, all proofs are interchangeable up to equality —
but Coq does *not* make this judgmental. Sketches the trade-offs and
where it matters (typeclass coherence, proof-carrying code).

## Chapter 2 — Induction

### 2.1 Inductive types

#### 2.1.1 Booleans

`Inductive bool : Set := true | false.` plus the standard
`if-then-else` desugaring to `match ... with`. The point is that the
constructors generate the inhabitants and a recursion/induction
principle (`bool_ind`, `bool_rec`) is auto-generated.

#### 2.1.2 Natural numbers

`Inductive nat : Set := O : nat | S : nat -> nat.`

Functions defined by `Fixpoint`:

```coq
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O    => m
  | S n' => S (plus n' m)
  end.
```

Termination is enforced by structural decrease on a parameter (`n`
above). Tactics specific to `nat`: `simpl`, `lia` (for arithmetic
goals — this requires `Require Import Lia.`).

#### 2.1.3 Simple proofs by induction

`induction n` performs case analysis on the constructors of `nat`,
yielding a base case (`n = O`) and a step case with an induction
hypothesis on `n'`. A typical proof of associativity of `plus`:

```coq
Lemma plus_assoc : forall a b c, a + (b + c) = (a + b) + c.
Proof.
  induction a; intros; simpl; [reflexivity | f_equal; auto].
Qed.
```

#### 2.1.4 Discriminate

`discriminate` closes a goal whose hypotheses contain an equality
between distinct constructors (e.g. `S n = O`). Behind the scenes it
exhibits a function that distinguishes the two and derives `False`.

### 2.2 Logic programming with `auto`

`auto` is a depth-bounded backward proof search using the global
hint database. Hint hooks: `Hint Resolve`, `Hint Rewrite`, `Hint
Constructors`, etc. (in modern Coq, prefix with `#[export]` to
control scope). `auto with arith` and `auto with sets` add more
specialised lemma sets.

`eauto` is `auto` with existential metavariables enabled, i.e. it
can introduce unification variables for missing arguments and try
to instantiate them later. Useful for proofs about relations.

## Chapter 3 — Modules

Brief, practical chapter.

- **3.1 Library modules.** `Require Import M.` loads the module `M`
  and brings its names into scope. `Require M.` loads it but keeps
  it qualified.
- **3.2 Your own modules.** A `.v` file *is* a module; section names,
  filenames, and module qualifiers stack uniformly.
- **3.3 Managing the context.** Quick reference for `Print`,
  `Search`, `SearchAbout`, `Show`, `Locate`, and the like — the
  bread-and-butter introspection commands.
- **3.4 Now you are on your own.** Closing pep talk pointing at the
  Reference Manual, the standard library, and the Coq community for
  next steps.

## Pointers for further reading

The tutorial itself recommends, after finishing it:

1. The Coq Reference Manual — exhaustive command and tactic reference.
2. The standard library — read it to absorb idioms.
3. Bertot & Castéran, *Interactive Theorem Proving and Program
   Development. Coq'Art: The Calculus of Inductive Constructions*
   (Springer, 2004) — a textbook treatment.
4. Pierce et al., *Software Foundations* — interactive, larger-scale,
   more recent.

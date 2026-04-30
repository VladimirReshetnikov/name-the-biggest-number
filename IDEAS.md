# Ideas for Beating the Current Contender

The current contender is not merely another named fast-growing function. It is
already a small "largest definable number" construction:

```coq
Definition contender_5 : nat := largest_STLCNatRec_nat_of_depth 42.
```

That is, it enumerates all shallow terms in the STLC+NatRec object language,
evaluates the closed terms that return `nat`, and takes the largest result.
This is a constructive, total-language analogue of the Busy Beaver or Rayo
"maximize over descriptions" move.

So the next serious contender should beat the method, not just the value. A
good plan is:

1. Define a new total object language `L6`.
2. Prove every current STLC+NatRec term embeds into `L6`.
3. Add one genuinely stronger compact construct to `L6`.
4. Define the new contender as the largest natural produced by any shallow
   `L6` term.
5. Prove the old winner embeds into `L6`, then apply the new construct to it
   inside `L6`.

The definition should have the shape:

```coq
Definition contender_6 : nat :=
  largest_L6_nat_of_depth 44.
```

The old contender should not appear in this definition. It should only appear
in the proof, where the witness term is morally:

```coq
Grow (embed old_best)
```

The proof then has the shape:

```coq
eval_L6 (Grow (embed old_best)) = Grow contender_5
Grow contender_5 > contender_5
eval_L6 (Grow (embed old_best)) <= contender_6
```

Therefore:

```coq
Theorem contender_5_lt_contender_6 :
  contender_5 < contender_6.
```

The easiest useful `Grow` is a primitive total fast-growing function, for
example an Ackermann-style iterator:

```coq
Grow x := ack 5 42 (S x)
```

or a repeated variant:

```coq
Grow x := Nat.iter (S x) (fun y => ack 5 42 (S y)) (S x)
```

That already gives a large formal margin over `contender_5`, and the proof
obligation `x < Grow x` should be straightforward.

The more satisfying version is to make `Grow` a principled ordinal-indexed
fast-growing hierarchy primitive:

```coq
tFGH : ordinal_notation -> term
```

The ordinal notation could start with Cantor normal forms below `epsilon_0`,
or use a stronger but still finitary notation if the formalization remains
manageable. Then `Grow x = FGH(big_ordinal, x)` is not merely a hand-picked
wrapper around the old result; it is a compact, total recursion principle that
strictly extends the previous object language.

A cheap move would be:

```coq
largest_STLCNatRec_nat_of_depth 43
```

The existing monotonicity proof almost gives this immediately, but it feels
like a parameter bump. It is probably legal, but not glorious.

The best next contender is therefore:

```text
largest value produced by a shallow term in STLC+NatRec plus a principled
stronger total recursor.
```

This keeps the constructive/no-axioms discipline, avoids Busy Beaver halting
problems, avoids mentioning `contender_5` in the definition of `contender_6`,
and wins by a structural embedding proof rather than by a small arithmetic
one-up.

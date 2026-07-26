# Lemma implementation plans

This directory contains one implementation plan for each declaration that currently ends in
`sorry`. Plans are grouped by expected implementation difficulty, including the supporting API
that the declaration will force us to build. Completed declarations are removed from this
inventory; any remaining cleanup is tracked separately in `refactoring-plans/`.

## Shared bound policy

The project does not need usable numerical estimates. Quantitative bounds should therefore follow
mathlib's existential Hales--Jewett construction rather than attempt to reproduce enormous closed
forms.

1. Define a predicate saying that a dimension `n` is sufficient.
2. Prove `∃ N, ∀ n ≥ N, Sufficient n`. For coloring arguments, obtain one finite coordinate type
   from `Combinatorics.Line.exists_mono_in_high_dimension`, transport it to `Fin N`, and prove
   upward closure by fixing all added coordinates.
3. Define the exposed bound transparently with `Nat.find` (or `Classical.choose` when leastness is
   irrelevant).
4. Immediately prove a `...Bound_spec` theorem and use only that theorem downstream.
5. If existence depends on a proposition such as `HasDensityHJ k`, define the bound using
   `if h : HasDensityHJ k then ... else 0`; theorem proofs already receive the positive branch as a
   hypothesis.

Use `noncomputable def`, not a bare `opaque`, so the chosen witness remains connected to its
specification. The coloring wrapper assumes a nonempty alphabet; this makes padding dimensions
upward safe even when the color type is empty.

## Inventory

- `easy/`: 0 plans
- `medium/`: 0 plans
- `hard/`: 0 plans
- `very-hard/`: 0 plans

One declaration still ends in `sorry` without a plan in this directory:
`DensityHalesJewett.GrahamRothschild.lines`, together with the `opaque` stand-in
`GrahamRothschild.bound`, left by the removal of the false focusing and canonization arguments.

Within a difficulty level, the plans should still be attempted in source dependency order:
`Word`, `Subspace`, `GrahamRothschild`, `UniformFibers`, `Insensitive`, `DensityIncrement`, `Main`,
then `Szemeredi`.

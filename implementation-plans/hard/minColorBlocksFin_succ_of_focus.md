# `DensityHalesJewett.FiniteUnions.minColorBlocksFin_succ_of_focus`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Feasibility audit

The previous plan was not a proof. If a binary focused line has variable set `D` and fixed-one
set `S`, focusing gives

`χ(S ∪ U) = χ(S ∪ D ∪ U)`

for every old profile `U`. It does not give `χ(U) = χ(D ∪ U)`. The fixed stem cannot simply be
discarded:

- adding `S` to the new block handles unions which contain the new index but not unions which omit
  it;
- adding `S` to every old block destroys disjointness and strict block order;
- applying the induction hypothesis to `U ↦ χ(S ∪ U)` controls only stemmed unions;
- placing the new block last preserves the old minimum but does not remove the same stem mismatch.

Thus `FiniteUnions.focus` with the stated profile type does not prove this recurrence. Before this
lemma can be implemented, either the statement needs a stronger anchored-focus hypothesis or the
finite-unions proof must be replaced.

## Feasible replacement argument

A non-circular replacement is the compactness consequence of infinite Hindman:

1. Prove an infinite ordered-block theorem for a coloring
   `χ∞ : Finset ℕ → Fin colors`. Apply `Hindman.FP_partition_regular` to the free semigroup
   `List ℕ` under append and the stream `n ↦ [n]`. Intersect each color class with the `FP`-set of
   this stream. Membership in that `FP`-set implies that the list is nonempty and strictly
   increasing. Since every finite product from the resulting stream remains in one color class,
   the first `s` lists give nonempty, pairwise ordered finite blocks whose every nonempty union is
   monochromatic.
2. Derive a finite dimension by compactness. If every `L` admitted a bad coloring, choose one
   `χL`. Let `U` be `Filter.hyperfilter ℕ`. For each finite `S : Finset ℕ`, the values of `χL` on
   `S` are defined for all sufficiently large `L`; `Ultrafilter.eventually_exists_iff` selects
   their eventual color and defines `χ∞ S`.
3. Apply the infinite theorem to `χ∞`. There are finitely many unions of the first `s` blocks, so
   their eventual-agreement sets have an intersection in `U`. Intersect once more with the
   at-top condition that all block coordinates are below `L`. Choosing such an `L` transports the
   blocks to `Fin L`, contradicting that `χL` was bad.
4. The monochromatic conclusion is stronger than `MinColorBlocksFin`: take `κ` to be the constant
   color. This route should replace the whole `MinColorBlocksFin` recurrence rather than attempt
   to implement the false stem rewrite.

## Lean helper boundaries

- `fp_singleton_nats_ordered`: membership in the `FP`-set of `n ↦ [n]` implies nonempty strict
  increase.
- `fp_selected_product`: an increasing nonempty finite set of stream indices gives an `FP`
  product.
- `exists_infinite_mono_ordered_blocks`: the Hindman application and list-to-finset transport.
- `eventual_badColor_eq`: ultrafilter stabilization for one finite subset.
- `exists_finite_mono_ordered_blocks`: compactness and final transport to `Fin L`.

## Verification

Import `Mathlib.Combinatorics.Hindman` and the ultrafilter/cofinite API privately. Build
`DensityHalesJewett.GrahamRothschild` with normal heartbeats and ensure the old focusing recurrence
is removed once the replacement theorem is connected.

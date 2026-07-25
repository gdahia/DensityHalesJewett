# `DensityHalesJewett.exists_density_increment_subspace_of_structured_correlation`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed reduction of
`density_increment`.

## Plan

Set `β := γ² / (4*k)`. Derive the positivity and upper bounds required by
`IsInsensitive.exists_disjoint_subspaces_iInter`, and use the lower density bound on
`intersection D` to verify `2*k*β ≤ dens (intersection D)`. Apply the tiling theorem with `r = k`
to obtain pairwise-disjoint `d`-subspaces contained in the intersection whose uncovered part has
density below `2*k*β = γ²/2`.

Let `T` be the union of the tile ranges. Convert containment and the uncovered estimate into

```text
dens(T) ≥ dens(intersection D) - γ²/2.
```

Use the structured-correlation inequality and the trivial bound on `A` inside the uncovered part
to prove

```text
dens(A ∩ T) ≥ (δ + γ/2) * dens(T).
```

Express both sides as sums over the finite pairwise-disjoint tile family. If every tile had
smaller relative density, summing would contradict this inequality, so select one tile `W` with
the desired density. Finally compose `W` with the outer subspace `V` and prove the evaluation and
relative-density identities needed to transport the estimate to the ambient cube.

## Verification

Isolate the union-density identities and composition identity inside the proof, but do not add
more named declarations unless they are reused. Build `DensityHalesJewett.DensityIncrement` with
normal heartbeats and resolve all non-`sorry` warnings and `info:` messages.

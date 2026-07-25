# `DensityHalesJewett.firstFailurePiece_density_sums`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Use `firstFailurePiece_biUnion` and `firstFailurePiece_pairwiseDisjoint` to express the complement
of `IsInsensitive.intersection C` as the disjoint union of the first-failure pieces. Apply the
finite disjoint-union cardinality theorem and divide by the ambient cardinality to obtain the first
density sum.

Intersect every piece with `A`; pairwise disjointness and the union identity are preserved. Apply
the same argument for the second density sum.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

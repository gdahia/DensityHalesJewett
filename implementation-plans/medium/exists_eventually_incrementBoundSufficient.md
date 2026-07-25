# `DensityHalesJewett.exists_eventually_incrementBoundSufficient`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Under the positivity and density-Hales--Jewett hypotheses carried by
`IncrementBoundSufficient`, choose a working parameter dimension `m` at least
`insensitiveIntersectionDimension k δ` and
`IsInsensitive.intersectionTilingBound k k d (γ² / (4k))`, as well as at least one.

Choose the eventual ambient threshold to be `manyLinesBound k m δ`. Every larger ambient
dimension then satisfies the predicate with this same `m`. Outside the positive branch, discharge
the conditional predicate directly.

## Verification

Keep selection of `m` separate from selection of the ambient threshold. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

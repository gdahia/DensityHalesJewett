# `DensityHalesJewett.exists_finite_structured_tiling`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Set `β := Parameters.γ k δ ^ 2 / (4*k)`. Derive its positivity and upper bounds, and use
`hDdense` to verify `2*k*β ≤ dens (intersection D)`. Apply
`IsInsensitive.exists_disjoint_subspaces_iInter` with `r = k`.

Convert the returned finite set to a `Finset`, preserve containment and pairwise-disjointness, and
simplify `2*k*β` to `γ²/2`. Show the tile family is nonempty from the positive lower density of the
intersection and the strict uncovered estimate.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

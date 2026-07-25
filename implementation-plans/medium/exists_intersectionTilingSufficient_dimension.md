# `DensityHalesJewett.IsInsensitive.exists_intersectionTilingSufficient_dimension`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Induct on `r`. For one family, identify `intersection D` with `D 0` and use
`exists_disjoint_subspaces`. For a successor, first tile the initial intersection by sufficiently
large outer subspaces.

Pull the last insensitive family back to each outer parameter cube using
`parameterPreimage_isInsensitive`. Discard outer tiles on which its pullback density is below
`2β`; tile every other pullback by `m`-subspaces and compose using
`composed_inner_tiles_facts`. Flatten the finite families. Outer disjointness handles different
parents, and the composed-inner lemma handles a common parent. Sum the first-stage and discarded
errors to obtain `< 2*(r+1)*β`.

## Verification

Keep the global disjointness split and density-error sum explicit. Build
`DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry` diagnostics.

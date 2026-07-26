# `DensityHalesJewett.GrahamRothschild.exists_locally_canonizing_extension`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed reduction of
`locallyCanonizingDimension_step`.

## Plan

Fix the old witness dimension `N`. Choose fresh coordinate packets recursively so that every
finite profile needed below can be focused. A profile records both possible statuses of the new
parameter coordinate (fixed and variable), every old parameter-line context, and the resulting
ambient line colors.

Use `hN` on the induced old-coordinate colorings and `FiniteUnions.focus` on the fresh packet,
nesting the resulting subspaces so that all profile equalities hold simultaneously. Assemble the
old subspace and the focused packet into a subspace with `blocks + 1` parameters.

Unfold `IsLocallyCanonizing` and split the exceptional coordinate. For an old coordinate, use the
corresponding local-canonization equality retained in the profile. For the new coordinate, use
the focusing equality. In both cases, normalize `Subspace.mapLine`, `variableSet`, coordinate-sum
reindexing, and the agreement of all other parameter coordinates.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

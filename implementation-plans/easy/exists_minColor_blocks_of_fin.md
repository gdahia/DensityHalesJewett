# `DensityHalesJewett.FiniteUnions.exists_minColor_blocks_of_fin`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Transport the coloring through `Fintype.equivFin C`, apply the supplied finite-cardinal theorem,
and map the resulting `κ` back through the inverse color equivalence. Injectivity of the
equivalence transports the min-color equality.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

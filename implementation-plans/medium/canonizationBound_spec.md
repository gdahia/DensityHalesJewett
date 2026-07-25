# `DensityHalesJewett.GrahamRothschild.canonizationBound_spec`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Use nontriviality to obtain `2 ≤ Fintype.card α`, unfold `canonizationBound`, and apply the
`Nat.find` specification at `n`. Transport the coloring to `Fin (card α)` and `Fin (card C)` using
`Fintype.equivFin`, then map the resulting subspace back to `α`.

Transport line evaluation and local canonization through the alphabet and color equivalences.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

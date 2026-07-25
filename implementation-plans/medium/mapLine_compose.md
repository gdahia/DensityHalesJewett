# `DensityHalesJewett.GrahamRothschild.mapLine_compose`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed reduction of
`exists_ordered_block_subspace`.

## Plan

Apply line extensionality and compare the two lines coordinatewise. Unfold `Subspace.mapLine` and
`Subspace.compose`, then split on the outer subspace's `idxFun` value. A fixed coordinate is fixed
on both sides; a parameter coordinate reduces to the corresponding coordinate of the line mapped
through `W`.

If unfolding the line equivalence is noisy, instead use equality of evaluations at every alphabet
letter together with `Subspace.compose_apply`, then invoke line extensionality.

## Verification

Use `simp only` for the coordinate cases. Build `DensityHalesJewett.GrahamRothschild` without
increasing heartbeats and resolve all non-`sorry` diagnostics attributed to the helper.

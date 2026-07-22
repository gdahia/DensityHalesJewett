# `DensityHalesJewett.GrahamRothschild.variableSet_nonempty`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed reduction of
`exists_ordered_block_subspace`.

## Plan

Take a variable coordinate from `l.proper`. Its `idxFun` value is `none`, so it belongs to the
filtered universal finset defining `variableSet l`.

## Verification

Unfold only `variableSet`, use the proper coordinate directly, and build
`DensityHalesJewett.GrahamRothschild` with normal heartbeats.

# `DensityHalesJewett.GrahamRothschild.variableSet_mapLine_of_indexed_blocks`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed reduction of
`exists_ordered_block_subspace`.

## Plan

Prove finset equality extensionally. A coordinate is variable in `Subspace.mapLine W l` exactly
when `W.idxFun` assigns it a direction `j` that is variable in `l`. Use `hW` to replace assignment
of direction `j` by membership in `B j`; this is precisely membership in
`(variableSet l).biUnion B`.

## Verification

Normalize `variableSet`, `Subspace.mapLine`, and biunion membership only after fixing a coordinate.
Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve every non-`sorry`
diagnostic attributed to the helper.

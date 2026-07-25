# `DensityHalesJewett.GrahamRothschild.exists_subspace_indexed_by_ordered_blocks`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed reduction of
`exists_ordered_block_subspace`.

## Plan

First prove that two distinct ordered blocks are disjoint: orient their indices and contradict the
strict coordinate ordering if a coordinate belongs to both. Choose one fixed alphabet letter for
coordinates outside all blocks. At a coordinate in a block, assign the unique corresponding
parameter direction; otherwise assign the fixed letter.

Use block nonemptiness to prove that every parameter direction occurs. Prove the displayed
`idxFun` characterization in both directions using uniqueness of the block index.

## Verification

Keep block-index uniqueness local to the construction. Build
`DensityHalesJewett.GrahamRothschild` without increasing heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

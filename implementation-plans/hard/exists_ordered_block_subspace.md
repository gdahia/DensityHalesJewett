# `DensityHalesJewett.GrahamRothschild.exists_ordered_block_subspace`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Supporting helper for the line case of the
Graham--Rothschild theorem.

## Plan

Use the strict ordering hypothesis to prove that distinct blocks are disjoint. Define the index
word of `W` by assigning direction `j` at every coordinate in `B j` and a fixed alphabet letter
outside the union of all blocks. Prove uniqueness of the block index from disjointness, and use the
nonemptiness of `B j` to establish `W.proper j`.

For a parameter line `l`, take `I := variableSet l`. Its properness makes `I` nonempty. Unfold the
index words of `W` and `Subspace.mapLine` coordinatewise to prove
`variableSet (Subspace.mapLine W l) = I.biUnion B`. Finally prove that mapping `l` through
`Subspace.compose V W` agrees with first mapping it through `W` and then through `V`, using line
extensionality and the existing evaluation lemmas.

## Verification

Isolate block-index uniqueness before defining `W`, and use `simp only` for the coordinate
calculation. Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all
non-`sorry` diagnostics.

# `DensityHalesJewett.Subspace.uniformFibersFinSufficient_of_iterationParameters`

Source: `DensityHalesJewett/UniformFibers.lean`. Extracted from the completed reduction of
`exists_uniformFibersFinSufficient_block_iteration`.

## Plan

Represent the prefix `Fin (fuel * dimension)` as `fuel` consecutive blocks of size `dimension`.
Induct through those blocks while maintaining a fixed word on the used blocks and a lower bound
equal to the original section density plus the number of failed stages times `increment`.

At the next block, enumerate its `alphabet ^ dimension` words. If every corresponding suffix fiber
is at least the current density minus `ε`, expose that block as the coordinate subspace and pad all
other prefix coordinates by the maintained fixed word. Otherwise, average the block fibers.
`block_loss` turns the failed fiber into another block word whose section density rises by at
least `increment`; fix that word and continue.

After `fuel` failures, `exhausts` makes the maintained density greater than one, contradicting
`Finset.dens_le_one`. Treat empty word spaces definitionally during the same induction rather than
adding a separate alphabet-cardinality theorem.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

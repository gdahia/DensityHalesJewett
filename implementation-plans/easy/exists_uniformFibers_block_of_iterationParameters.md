# `DensityHalesJewett.Subspace.exists_uniformFibers_block_of_iterationParameters`

Source: `DensityHalesJewett/UniformFibers.lean`. Extracted from the completed outer-quantifier
reduction of `uniformFibersFinSufficient_of_iterationParameters`.

## Plan

Split `Fin (fuel * dimension)` into consecutive blocks and induct on `parameters.fuel`. At one
stage, expand the density of the current section as the average of the
`alphabet ^ dimension` block fibers. If every fiber is above the required threshold, expose that
block and use `padPrefixSubspace`; otherwise choose a denser block word using
`parameters.block_loss` and continue with one less block.

The terminal branch contradicts `Finset.dens_le_one` using `parameters.exhausts`. The only
remaining obligations are the block-sum `Fin` equivalences, the fiber-density averaging identity,
and linear arithmetic from `block_loss` and `exhausts`.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

# `DensityHalesJewett.Subspace.exists_uniformFibersFinSufficient_block_iteration`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Let `s := alphabet ^ dimension` and choose a positive increment `ρ` small compared with `ε / s`.
Choose fuel with `fuel * ρ > 1`, and take the ambient prefix to be the corresponding concatenation
of `dimension`-coordinate blocks.

Induct on the fuel while maintaining a fixed initial word, the unused blocks, and a lower bound on
the density of the current section.  On the next block, enumerate its `s` words.  If every
associated suffix fiber is at least the current density minus `ε`, the block itself is the desired
subspace.  Otherwise, fiber averaging and the failed word give a fixed block word whose section
density rises by at least `ρ`; continue with one less block.

Fuel exhaustion gives density greater than one, contradicting `Finset.dens_le_one`.  Handle
`alphabet = 0` and `s = 1` before the iteration, where parameter words are empty or unique.

## Verification

Keep the induction invariant as a structure or a single conjunction, and prove the one-block
averaging inequality separately.  Build `DensityHalesJewett.UniformFibers` with normal heartbeats
and resolve all non-`sorry` diagnostics.

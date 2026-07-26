# `DensityHalesJewett.Subspace.exists_uniformFibersIterationParameters`

Source: `DensityHalesJewett/UniformFibers.lean`. Extracted from the completed reduction of
`exists_uniformFibersFinSufficient_block_iteration`.

## Plan

Let `s := alphabet ^ dimension`. Choose a positive increment `ρ` with `s * ρ ≤ ε`: use `ε / 2`
when `s = 0`, and `ε / (2 * s)` otherwise. Archimedean unboundedness of the natural numbers gives
`fuel` with `1 < fuel * ρ`. Package these inequalities into
`UniformFibersIterationParameters`.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

# `DensityHalesJewett.exists_dense_tile_of_density_sum`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Argue by contradiction that if every tile had relative pullback density below
`δ + Parameters.γ k δ / 2`, multiplying by the common positive tile-range density and summing
would contradict the aggregate inequality. Convert intersection-with-range density to
`Subspace.relativeDensity` using injectivity of subspace evaluation.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

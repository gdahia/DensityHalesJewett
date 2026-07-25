# `DensityHalesJewett.Subspace.exists_restricted_parameters_with_dense_fibers`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Apply `exists_fibers_dense` with error `δ / 2`. The hypotheses `0 < δ` and `δ ≤ 1` verify the
strict error bounds, while the ambient density lower bound converts the uniform fiber estimate
into `δ / 2 ≤ dens (fiber A (W x))`. Specialize this estimate to parameter words restricted along
`Fin.castSuccEmb`.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics.

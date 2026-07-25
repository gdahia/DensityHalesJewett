# `DensityHalesJewett.restrictedParameterWords_density_le_eta`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Identify `restrictedParameterWords k m` with the image of `(Fin m → Fin k)` under
`Fin.castSuccEmb`. Its density in the `(k+1)`-letter parameter cube is `(k / (k+1)) ^ m`. Use the
geometric-decay specification encoded by `insensitiveIntersectionDimension` and
`hm_large` to bound this by `Parameters.η k δ`.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

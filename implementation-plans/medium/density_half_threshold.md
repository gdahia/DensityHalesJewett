# `DensityHalesJewett.density_half_threshold`

Source: `DensityHalesJewett/DensityIncrement.lean`. Numerical helper for “Many lines in a dense
slice.”

## Plan

Apply `density_ge_threshold f θ (θ/2)` using the supplied `[0,1]` bounds. It gives the stronger
lower bound `(θ/2)/(1-θ/2)`. Prove this is at least `θ/2` from `0 < θ` and `θ ≤ 1`, and finish by
transitivity.

## Verification

Keep all divisions in ordered-field form and discharge denominator positivity explicitly. Build
`DensityHalesJewett.DensityIncrement`.

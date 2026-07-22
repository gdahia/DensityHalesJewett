# `DensityHalesJewett.density_near_average`

Source: `DensityHalesJewett/DensityIncrement.lean`. Numerical helper for “Many lines in a dense
slice.”

## Plan

Let `H = {x | δ - 2*η ≤ f x}`. Bound `f` by `δ - 2*η` off `H` and by
`δ + η^2/2` on `H`, then average this pointwise bound. Combine it with the lower bound
`δ - η^2/2 ≤ 𝔼 x, f x`. If `dens H < 1-η`, the resulting real inequality contradicts
`0 < η`; close the final polynomial estimate with `nlinarith` after establishing the signs of all
factors.

## Verification

Do not specialize this lemma to densities. Build `DensityHalesJewett.DensityIncrement`.

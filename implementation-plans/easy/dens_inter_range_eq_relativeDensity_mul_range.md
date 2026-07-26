# `DensityHalesJewett.Subspace.dens_inter_range_eq_relativeDensity_mul_range`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed reduction of
`exists_dense_tile_of_density_sum`.

## Plan

Unfold `Subspace.relativeDensity`, `Subspace.range`, and `Finset.dens`. Injectivity of `W`
identifies `A ∩ Subspace.range W` with the image under `W` of the filtered parameter cube.
Rewrite the two image cardinalities using `Finset.card_image_iff.mpr (Subspace.injective W)` and
cancel the parameter-cube cardinality.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

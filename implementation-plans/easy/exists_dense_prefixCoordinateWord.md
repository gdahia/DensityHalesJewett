# `DensityHalesJewett.exists_dense_prefixCoordinateWord`

Source: `DensityHalesJewett/Main.lean`. Extracted from the completed reduction of
`exists_density_preserving_subspace_of_le`.

## Plan

Transport `A` along `prefixCoordinateEquiv hmn`, with the suffix coordinates first. Apply
`average_density_fiber` to express the ambient density as the average of the densities obtained
by fixing a suffix. Use `Finset.le_expect` contrapositively, or the standard existence-of-an-entry
above-the-average lemma, to select `y`.

Normalize membership through `prefixCoordinateWord`; no subspace reasoning remains.

## Verification

Build `DensityHalesJewett.Main` with normal heartbeats and resolve all non-`sorry` diagnostics
attributed to the helper.

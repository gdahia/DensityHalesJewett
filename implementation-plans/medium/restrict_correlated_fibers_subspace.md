# `DensityHalesJewett.restrict_correlated_fibers_subspace`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Embed `Fin m` into `Fin M` using `m ≤ M` and construct the corresponding coordinate-restriction
subspace. Compose it with `W`. Direct evaluation identities show that the uniform fiber estimates
and every good restricted-alphabet parameter line are inherited by the composite.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

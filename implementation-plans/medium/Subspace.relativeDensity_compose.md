# `DensityHalesJewett.Subspace.relativeDensity_compose`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Unfold `Subspace.relativeDensity`, `pullback`, and `Subspace.compose`. Extensionality of the two
filtered parameter-word finsets reduces the claim to the evaluation identity
`compose V W x = V (W x)`.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

# `DensityHalesJewett.incrementBound_spec`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed reduction of
`density_increment`.

## Plan

First prove an eventual density-increment dichotomy under `HasDensityHJ k`. For each sufficiently
large ambient dimension, select a working parameter dimension `m` which is large enough for
`insensitiveIntersectionDimension` and for
`IsInsensitive.intersectionTilingBound k k d (γ² / (4k))`. Require the ambient dimension to be
large enough for `manyLinesBound k m δ`.

Package this nested choice as an eventual statement, then define `incrementBound k d δ` by
conditional `Nat.find` on the relevant positivity hypotheses and `HasDensityHJ k`. The positive
branch should expose exactly the four inequalities in this specification theorem; harmless
defaults may be used outside that branch.

## Verification

Keep the eventual theorem separate from the transparent `Nat.find` definition. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve every non-`sorry`
diagnostic attributed to the module.

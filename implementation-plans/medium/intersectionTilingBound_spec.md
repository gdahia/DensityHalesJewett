# `DensityHalesJewett.IsInsensitive.intersectionTilingBound_spec`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Unfold `intersectionTilingBound`, select the positive branch using the five hypotheses, and apply
`Nat.find_spec` from `exists_eventually_intersectionTilingSufficient` at `n`.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

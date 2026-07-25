# `DensityHalesJewett.IsInsensitive.tilingBound_spec`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Unfold `tilingBound`, select the positive branch from `hm`, `hβ₀`, and `hβ₁`, and apply
`Nat.find_spec` from `exists_eventually_tilingSufficient` at `n`.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

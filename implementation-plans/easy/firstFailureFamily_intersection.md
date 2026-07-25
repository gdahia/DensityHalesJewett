# `DensityHalesJewett.firstFailureFamily_intersection`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Extensionality reduces the equality to membership. Unfold `firstFailureFamily`,
`firstFailurePiece`, and `IsInsensitive.intersection`; split indices according to `< i`, `= i`,
or `> i`. The intersection conditions become exactly failure of `C i` and membership in every
earlier `C j`.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

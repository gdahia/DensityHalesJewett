# `DensityHalesJewett.firstFailurePiece_biUnion`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

For forward membership, a point in a first-failure piece fails one member of `C`, so it is outside
the indexed intersection. Conversely, for a point outside the intersection, choose the least
index at which membership fails. Minimality gives membership in every earlier set, placing the
point in that first-failure piece.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

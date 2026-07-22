# `DensityHalesJewett.firstFailurePiece_biUnion`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`firstFailureFamily_facts` reduction.

## Plan

Prove finset equality by membership. Membership in any first-failure piece directly contradicts
membership in the full intersection. Conversely, for a point outside the intersection, use the
finite linear order on `Fin k` to choose the least index at which membership in `C` fails. The
minimality condition supplies membership in every earlier `C j`, placing the point in the selected
`firstFailurePiece` and hence in the indexed union.

## Verification

Isolate only the least-failing-index selection needed by the reverse implication. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

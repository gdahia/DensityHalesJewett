# `DensityHalesJewett.firstFailurePiece_disjoint_of_lt`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed reduction of
`firstFailurePiece_pairwiseDisjoint`.

## Plan

Assume a word belongs to both the `i`-piece and the `j`-piece, where `i < j`. Membership in the
`i`-piece says that the word is not in `C i`, while membership in the `j`-piece says that it is in
every `C`-set at an earlier index, hence in `C i`. Use this contradiction to prove the two coerced
finsets are disjoint as sets.

## Verification

Unfold `firstFailurePiece` only after introducing a hypothetical common member. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

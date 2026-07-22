# `DensityHalesJewett.firstFailurePiece_pairwiseDisjoint`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`firstFailureFamily_facts` reduction.

## Plan

Take distinct indices `i` and `j` and orient them using linearity. If `i < j`, membership in the
`j`-piece forces membership in `C i`, whereas membership in the `i`-piece forces nonmembership in
`C i`; the case `j < i` is symmetric. Use this contradiction to prove the two coerced finsets are
disjoint as sets.

## Verification

Normalize membership in `firstFailurePiece` only after orienting the indices. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats.

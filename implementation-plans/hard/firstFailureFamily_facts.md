# `DensityHalesJewett.firstFailureFamily_facts`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`exists_structured_correlation` reduction.

## Plan

Prove the four coordinated facts about the first-failure construction:

1. `firstFailureFamily C i` remains insensitive at every index. Before `i`, use the supplied
   insensitivity of `C`; at `i`, use complement closure; after `i`, prove insensitivity of `univ`.
2. Its indexed intersection is exactly `firstFailurePiece C i`. Expand membership in the finite
   infimum and split indices according to `< i`, `= i`, and `i <`.
3. The union of all first-failure pieces is the complement of `intersection C`. In the reverse
   direction, choose the least failing index in the finite linear order `Fin k`.
4. The pieces are pairwise disjoint: if `i < j`, membership in the `j`-piece forces membership in
   `C i`, while membership in the `i`-piece forces nonmembership.

The least-index argument and the finite-infimum membership characterization are the main API work.
Avoid manufacturing one-use rewrite equalities; normalize membership goals and apply the relevant
finite-order lemmas directly.

## Verification

Build `DensityHalesJewett.DensityIncrement` and ensure the proof introduces no warnings or info
messages beyond the repository's intentional remaining `sorry` declarations.

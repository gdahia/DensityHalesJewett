# `DensityHalesJewett.firstFailureFamily_intersection`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`firstFailureFamily_facts` reduction.

## Plan

Prove finset equality extensionally and expand membership in `IsInsensitive.intersection`. In the
forward direction, specialize the intersection condition at `i` to obtain failure of membership
in `C i`, and at each `j < i` to obtain membership in `C j`. In the reverse direction, split an
arbitrary index `j` into `j < i`, `j = i`, and `i < j`; use the corresponding component of
`firstFailurePiece C i` in the first two cases, while the final case reduces to membership in
`Finset.univ`.

## Verification

Use the finite-infimum membership characterization directly and keep the three order cases
visible. Build `DensityHalesJewett.DensityIncrement` with normal heartbeats.

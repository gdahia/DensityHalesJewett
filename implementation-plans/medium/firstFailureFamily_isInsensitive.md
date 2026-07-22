# `DensityHalesJewett.firstFailureFamily_isInsensitive`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`firstFailureFamily_facts` reduction.

## Plan

Fix an index `j` and split according to `j < i`, `j = i`, or `i < j`. In the first case,
`firstFailureFamily C i j` is `C j`, so apply `hC j`. At the failure index it is `(C j)ᶜ`; unfold
`IsInsensitive` and use complement membership to transport `hC j`. After the failure index it is
`Finset.univ`, whose membership condition is immediate.

## Verification

Keep the order split explicit and normalize `firstFailureFamily` separately in each branch. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

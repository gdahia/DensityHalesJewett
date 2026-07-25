# `DensityHalesJewett.GrahamRothschild.exists_locally_canonizing_dimension`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Represent the ambient coordinates as an ordered sum of `blocks` packets. Select one line word in
each packet by reverse finite recursion. At a packet, color each constant packet word by its finite
profile over all earlier fixed words and all fixed-letter-or-variable choices in already selected
later packets. Apply `FiniteUnions.focus` to make this profile constant along a line.

Assemble the selected packet lines into a block subspace. The stored profile equality proves
`IsLocallyCanonizing`: changing one fixed parameter letter is exactly one focusing equality.

## Verification

Introduce only the finite profile encodings and block-sum evaluation lemmas needed by the reverse
recursion. Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all
non-`sorry` diagnostics.

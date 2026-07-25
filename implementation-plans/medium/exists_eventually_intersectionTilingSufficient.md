# `DensityHalesJewett.IsInsensitive.exists_eventually_intersectionTilingSufficient`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Obtain an exact dimension from `exists_intersectionTilingSufficient_dimension`. Pad to larger
dimensions by splitting off the exact coordinate prefix, applying the theorem in every fixed
extra-coordinate section, and prefixing the resulting tiles.

Flatten the sectionwise families; different fixed suffixes give disjoint ranges. Average the
sectionwise uncovered bounds to retain `< 2*r*β`.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

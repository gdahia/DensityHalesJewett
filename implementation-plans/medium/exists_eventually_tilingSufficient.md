# `DensityHalesJewett.IsInsensitive.exists_eventually_tilingSufficient`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Obtain an exact sufficient dimension from `exists_tilingSufficient_dimension`. For a larger
dimension, split off the exact prefix, fiber `D` over all assignments to the extra coordinates,
and apply exact tiling in every relevant section.

Prefix the resulting subspaces by their fixed extra-coordinate assignments. Distinct sections
give disjoint ranges; within one section use the exact theorem's disjointness. Sum the uncovered
estimates over sections to recover the same density bound.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

# `DensityHalesJewett.IsInsensitive.composed_inner_tiles_facts`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Finite image preserves finiteness. For containment, evaluate `compose V W` and use containment of
`W` in `parameterPreimage V D`. For pairwise-disjointness, pull an equality between two composite
range points back through injectivity of `V`, then apply pairwise-disjointness of the inner ranges.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

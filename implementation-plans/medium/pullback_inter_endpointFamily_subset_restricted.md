# `DensityHalesJewett.pullback_inter_endpointFamily_subset_restricted`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Suppose a word in the pullback and in every endpoint family uses `Fin.last k`. Regard that word as
the endpoint of the parameter line whose variable coordinates are exactly its final-letter
positions. Membership in every endpoint family supplies the first `k` points of the line, while
pullback membership supplies its endpoint. Mapping the line through `V` contradicts `hfree`.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

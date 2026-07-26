# `DensityHalesJewett.Subspace.average_restrictedParameterSlice`

Source: `DensityHalesJewett/UniformFibers.lean`. Extracted from the completed reduction of
`exists_dense_suffix_of_restricted_fibers`.

## Plan

Rewrite both densities as expectations of indicator functions. Commute the finite expectations
over restricted parameter words and suffix words with `Finset.expect_comm`. For each pair
`(x,y)`, simplify membership in `fiber A (W (Fin.castSucc ∘ x))`; both indicators test the same
word `concat (W (Fin.castSucc ∘ x)) y`.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

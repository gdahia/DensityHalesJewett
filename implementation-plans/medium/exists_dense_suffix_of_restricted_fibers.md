# `DensityHalesJewett.Subspace.exists_dense_suffix_of_restricted_fibers`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Double-count pairs of restricted parameter words and suffixes for which
`concat (W (Fin.castSucc ∘ x)) y ∈ A`. Average the pointwise fiber lower bounds over restricted
parameter words, commute the two finite sums, and select a suffix whose parameter slice has
density at least `δ / 2`.

## Verification

Use the existing fiber-average API. Build `DensityHalesJewett.UniformFibers` with normal heartbeats
and resolve all non-`sorry` diagnostics.

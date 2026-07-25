# `DensityHalesJewett.exists_dense_firstFailurePiece_of_density_sums`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Call a piece small when its density is below `Parameters.γ k δ`. Bound the sum of all small pieces
using the first defining term of `γ`. If every remaining piece had relative `A`-density below
`δ + γ`, sum those inequalities and use the two supplied density identities.

The global weighted correlation, the absolute lower bound, the intersection-density hypothesis,
and the remaining defining bounds on `γ` contradict that estimate. Keep the argument
division-free so empty pieces need no special case.

## Verification

Normalize the real inequalities directly and pass meaningful bounds explicitly to arithmetic
automation. Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all
non-`sorry` diagnostics.

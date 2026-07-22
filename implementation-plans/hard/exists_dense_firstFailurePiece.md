# `DensityHalesJewett.exists_dense_firstFailurePiece`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`exists_structured_correlation` reduction.

## Plan

Use `firstFailureFamily_facts` to partition the complement of `intersection C` into the pairwise
disjoint pieces `firstFailurePiece C i`. Convert the two hypotheses about
`A ∩ (intersection C)ᶜ` into sums of piece densities.

Call a piece small when its density is below `γ`. The total density of all small pieces is less
than `k * γ`, hence at most `δ * η²` by the first term in the definition of `γ`. If every large
piece had relative `A`-density below `δ + γ`, summing over small and large pieces would contradict
the global `(δ + 6η)` correlation. Use the absolute lower bound `δ - 3η`, the lower bound on
`dens (intersection C)`, and the other two defining bounds on `γ` to control the discarded mass.

Formulate the averaging step without division so empty pieces require no special relative-density
definition. Normalize the final real inequalities directly and pass all meaningful bounds to
`nlinarith` explicitly.

## Verification

Keep the partition-to-sum conversion separate from the real arithmetic inside the proof. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry` linter
output.

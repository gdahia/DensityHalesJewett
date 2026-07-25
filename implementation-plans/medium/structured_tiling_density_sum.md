# `DensityHalesJewett.structured_tiling_density_sum`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Let `T` be the union of the pairwise-disjoint tile ranges. Containment and the uncovered estimate
give `dens T ≥ dens (intersection D) - γ²/2`. Use the structured-correlation inequality and the
trivial upper bound on `A` in the uncovered part to prove
`dens (pullback V A ∩ T) ≥ (δ + γ/2) * dens T`.

Express both sides as sums over the finite pairwise-disjoint tile family, yielding the stated
aggregate inequality.

## Verification

Keep the union-density identities separate from the real arithmetic. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

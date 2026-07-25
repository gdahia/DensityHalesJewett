# `DensityHalesJewett.line_or_density_increment_chain`

Source: `DensityHalesJewett/Main.lean`.

## Plan

Induct on `j ≤ R`, maintaining either an ambient line or a `d j`-subspace whose relative
`A`-density is at least `δ + j * (Parameters.γ k δ / 2)`. The zero case is `V₀`. At a successor
stage apply `density_increment_chain_step`; propagate its line alternative immediately or retain
its next subspace.

Specialize the invariant at `R`.

## Verification

Expose the induction invariant and keep each alternative explicit. Build `DensityHalesJewett.Main`
with normal heartbeats and resolve all non-`sorry` diagnostics.

# `DensityHalesJewett.density_increment_chain_step`

Source: `DensityHalesJewett/Main.lean`.

## Plan

Pull `A` back through `V` and apply `density_increment` at density floor
`δ + j * (Parameters.γ k δ / 2)` with target dimension `d (j+1)`. The schedule gives the ambient
dimension bound; positivity gives the target-dimension hypothesis, and the current invariant plus
`Finset.dens_le_one` supplies the upper density bound.

If the pullback contains a line, map it through `V`. Otherwise compose the increment subspace with
`V`. Use `Subspace.relativeDensity_compose` and `Parameters.γ_mono_lowerBound` to obtain the next
fixed-step lower bound.

## Verification

Keep line mapping and subspace composition as explicit subgoals. Build `DensityHalesJewett.Main`
with normal heartbeats and resolve all non-`sorry` diagnostics.

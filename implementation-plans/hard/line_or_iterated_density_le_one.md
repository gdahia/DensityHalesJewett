# `DensityHalesJewett.line_or_iterated_density_le_one`

Source: `DensityHalesJewett/Main.lean`. Extracted from the completed reduction of
`density_hales_jewett_fin`.

## Plan

Induct on the number of scheduled stages while maintaining a subspace of dimension `d j` whose
relative `A`-density is at least

```text
δ + j * (Parameters.γ k δ / 2).
```

At stage `j`, pull `A` back through the current subspace and apply `density_increment` at the
displayed density floor with target dimension `d (j + 1)`. The schedule supplies the dimension
bound and positivity supplies the target-dimension hypothesis. If the pullback contains a line,
compose that line with the current subspace to obtain an ambient line. Otherwise compose the new
parameter subspace with the current one.

Prove the pullback/relative-density identity for the composite and use
`Parameters.γ_mono_lowerBound` to replace the increment at the current floor by the fixed lower
bound `Parameters.γ k δ / 2`. If an intermediate floor already exceeds one, close immediately
using `Finset.dens_le_one`; otherwise continue the induction. At stage `R`, the same upper bound on
relative density gives the second disjunct.

## Verification

Keep line composition and relative-density composition as explicit local subgoals, and expose the
induction invariant rather than accumulating one-use facts. Build `DensityHalesJewett.Main` with
normal heartbeats and resolve every non-`sorry` warning or `info:` message.

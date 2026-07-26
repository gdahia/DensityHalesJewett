# `DensityHalesJewett.GrahamRothschild.locallyCanonizingDimension_step`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Choose a fresh coordinate packet large enough for `FiniteUnions.focus`.  Color packet words by
the complete finite profile consisting of all earlier parameter-line choices and all ambient
line colors produced by the already locally canonizing subspace from `h`.

Use the focused line as the new parameter block and compose it with the old block subspace.
Unfold `IsLocallyCanonizing`; if the changed fixed coordinate is old, apply `h`, and if it is the
new coordinate, apply the stored focusing equality.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

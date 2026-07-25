# `DensityHalesJewett.Subspace.uniformFibersBound_fin_spec`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Unfold `uniformFibersBound`, select the positive branch using the three hypotheses, and apply
`Nat.find_spec` from `exists_eventually_uniformFibersFinSufficient` at `n`.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics.

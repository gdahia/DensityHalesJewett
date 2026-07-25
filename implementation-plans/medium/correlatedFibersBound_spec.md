# `DensityHalesJewett.correlatedFibersBound_spec`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Choose a working dimension `M` at least both the requested output dimension `m` and
`Parameters.m₀ k δ`. Choose `L` large enough for `GrahamRothschild.lines_twoColor` at dimension
`M`, then require enough ambient coordinates for `Subspace.exists_fibers_dense` at dimension `L`
and error `Parameters.η k δ ^ 2 / 2`. Connect this eventual construction to the opaque
`correlatedFibersBound`.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

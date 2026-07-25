# `DensityHalesJewett.Subspace.suffixFunctionFintype`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Split on whether the prefix word type is inhabited. In the inhabited case, embed suffix functions
into full functions by adjoining a fixed prefix; in the empty case, use the resulting restrictions
on `ι` and the alphabet to give a direct finite instance.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics.

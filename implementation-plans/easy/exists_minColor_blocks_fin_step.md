# `DensityHalesJewett.FiniteUnions.exists_minColor_blocks_fin_step`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Choose the finite packet size required by `FiniteUnions.focus` for the profile indexed by all
unions of the existing `s` blocks.  Place those packets before a shifted copy of the blocks
supplied by `h`.  The variable packets of the focused line form the new first block; fixed packets
are absorbed into the profile stem.

For a nonempty union, split on whether it contains the new index.  The containing case is the
focusing equality; otherwise shift the index set and apply the old min-color identity.  Packet
order gives nonemptiness and strict block separation.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

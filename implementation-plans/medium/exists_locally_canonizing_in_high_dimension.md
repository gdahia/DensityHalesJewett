# `DensityHalesJewett.GrahamRothschild.exists_locally_canonizing_in_high_dimension`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Obtain an exact dimension from `exists_locally_canonizing_dimension`. For every larger `n`, split
`Fin n` into the selected prefix and unused final coordinates. Restrict the coloring by fixing the
extra coordinates at one alphabet letter, apply the exact theorem, and pad the resulting subspace.

Prove that mapping parameter lines through the padded subspace agrees with the restricted
coloring, so local canonization transports unchanged.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

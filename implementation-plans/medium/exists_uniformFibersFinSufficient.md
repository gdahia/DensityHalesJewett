# `DensityHalesJewett.Subspace.exists_uniformFibersFinSufficient`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Work entirely with `Fin` alphabets and coordinate blocks. Set `s := alphabet ^ dimension`, choose a
positive density increment `ρ`, and handle `s ≤ 1` separately. Iterate through disjoint
`dimension`-coordinate blocks with fuel greater than `1/ρ`.

At each stage, either every fiber above the free block is within `ε` below the current density, or
fiber averaging supplies another block word whose density is at least `ρ` larger. In the second
case fix that word and continue. Fuel exhaustion contradicts `Finset.dens_le_one`.

## Verification

Package the current fixed prefix, unused blocks, and density lower bound as the induction
invariant. Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all
non-`sorry` diagnostics.

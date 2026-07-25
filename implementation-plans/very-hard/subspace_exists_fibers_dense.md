# `DensityHalesJewett.Subspace.exists_fibers_dense`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Bound construction

Prove an eventual theorem by a finite fuel iteration, then select `uniformFibersBound` by
`Nat.find`. The bound may be extremely wasteful and depend only on alphabet cardinality, `m`, and
`ε`; its specification should transport arbitrary finite coordinate types through
`Fintype.equivFin` after carving out enough `m`-blocks.

## Plan

Set `s := card α ^ m` and choose a positive increment `ρ`; handle `s ≤ 1` separately because
`ε/(s-1)` degenerates. Iterate through disjoint blocks of `m` coordinates with fuel greater than
`1/ρ`.

At a stage, consider all fibers above the free block. If every density is at least the current
ambient fiber density minus `ε`, return that block as `V`. Otherwise fiber averaging implies that
some other block word has density at least the current density plus `ρ`; fix that word and continue
on the remaining coordinates. Maintain:

- the current suffix family is the appropriate iterated fiber of the original `A`;
- its density has increased by at least `stage * ρ`;
- the unused coordinate count still contains another full block.

Fuel exhaustion contradicts `Finset.dens_le_one`.

## Supporting API and verification

Develop reusable iterated-fiber and coordinate-sum reassociation lemmas first. This proof should
not manipulate `Fin (n-m)` directly. Build often; do not increase maximum heartbeats.

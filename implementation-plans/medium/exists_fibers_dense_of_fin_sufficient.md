# `DensityHalesJewett.Subspace.exists_fibers_dense_of_fin_sufficient`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Plan

Transport the alphabet along `Fintype.equivFin α` and the prefix coordinates along
`Fintype.equivFin ι`. Obtain a finite model for the suffix coordinates from the supplied finite
function spaces, handling the empty or subsingleton alphabet cases separately.

Map `A` to the resulting `Fin` word cube, apply `hfin`, and reindex the returned subspace back to
`α` and `ι`. Prove that evaluation, fibers, and density are preserved by the equivalences.

## Verification

Build `DensityHalesJewett.UniformFibers` with normal heartbeats and resolve all non-`sorry`
diagnostics.

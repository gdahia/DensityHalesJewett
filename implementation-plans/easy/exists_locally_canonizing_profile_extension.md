# `DensityHalesJewett.GrahamRothschild.exists_locally_canonizing_profile_extension`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed wrapper reduction
of `exists_locally_canonizing_extension`.

## Plan

Choose the finite profile types for fixed and variable status of the new parameter coordinate,
old parameter-line contexts, and their colors. Apply `FiniteUnions.focus` successively to those
finite profiles and use `hN` for the old-coordinate component.

Assemble the resulting old subspace and final focused line with `Subspace.concat` and `reindex`.
After unfolding `IsLocallyCanonizing`, split the exceptional `Fin (blocks + 1)` coordinate with
`Fin.lastCases`. The old branch is the hypothesis supplied by `hN`; the last branch is the
focused-profile equality. Each branch then closes by extensionality and the existing
`Subspace.mapLine` simplification lemmas.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

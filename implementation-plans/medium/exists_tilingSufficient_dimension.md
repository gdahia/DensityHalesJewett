# `DensityHalesJewett.IsInsensitive.exists_tilingSufficient_dimension`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Choose finitely many equal terminal coordinate blocks large enough for
`exists_restrictAlphabet_subset`. Recursively process unused blocks. If uncovered density is below
`2β`, stop. Otherwise threshold averaging gives many prefixes whose next-block fiber has density
at least `β`; apply the restricted-alphabet subspace theorem in each good fiber.

Pigeonhole over the finite type of block subspace structures. The common structure supplies a
positive-density family of mutually disjoint new subspaces contained in `D`. Maintain containment,
pairwise-disjointness, coverage gain, and the remaining-section insensitivity invariant. Density
bounded by one forces termination.

## Verification

Prove the finite cardinality bound for block subspace structures separately inside the proof.
Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

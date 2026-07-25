# `DensityHalesJewett.IsInsensitive.exists_disjoint_subspaces`

Source: `DensityHalesJewett/Insensitive.lean`.

## Bound construction

Prove a finite-stage tiling theorem with enough equal coordinate blocks and choose
`tilingBound k m β` from its eventual form. This existence uses the already chosen
`restrictAlphabetBound`; an explicit formula is unnecessary. Publish `tilingBound_spec`.

## Plan

Create a recursion over unused coordinate blocks. At each stage, if the uncovered density is below
`2β`, stop. Otherwise fiber over the next terminal block. Threshold averaging gives many prefixes
whose remaining fiber has density at least `β`. In each good fiber,
`exists_restrictAlphabet_subset` supplies an `m`-subspace whose first-`k` restriction lies in the
fiber; `(i,last k)`-insensitivity upgrades the entire `(k+1)`-alphabet subspace into `D`.

There are finitely many subspace structures in the block. Pigeonhole to obtain one structure for a
positive-density set of prefixes. The resulting prefixed subspaces are mutually disjoint and add a
fixed positive amount of fresh coverage.

Maintain an invariant recording finite family, containment, pairwise-disjoint ranges, coverage
gain, and insensitivity of every remaining section. Complements and unions use the existing Boolean
closure lemmas. Density bounded by one forces termination.

## Verification

Prove cardinality bounds for the finite type of subspace structures separately. Build
`DensityHalesJewett.Insensitive` without heartbeat changes.

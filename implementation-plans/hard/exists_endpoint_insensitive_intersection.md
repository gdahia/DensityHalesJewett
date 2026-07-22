# `DensityHalesJewett.exists_endpoint_insensitive_intersection`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from “A large insensitive
intersection.”

## Plan

For each complete restricted-alphabet parameter line, take its unique extension to the
`(k+1)`-letter cube and use its endpoint at `Fin.last k`. For every `i : Fin k`, define `C i` by
replacing every occurrence of the last letter in a parameter word by `i.castSucc` and testing
membership in `pullback V A`.

Prove directly that `C i` is `(i,last)`-insensitive and that their intersection consists of the
good endpoints together with the restricted-alphabet part of `pullback V A`. Injectivity of the
endpoint map, `Subspace.linesEquiv`, and the large-dimension hypothesis give density at least
`θ/4`.

If a word in both the intersection and `pullback V A` uses the last letter, its replacements give
the first `k` points of a complete ambient line and the word itself gives the endpoint,
contradicting `hfree`. Thus this intersection lies in the restricted-alphabet cube. Use the
geometric-decay part of `insensitiveIntersectionDimension` to bound its density by `η`.

## Verification

Separate the replacement simp lemmas, endpoint injectivity, and restricted-cube cardinality
calculation. Build `DensityHalesJewett.DensityIncrement` with normal heartbeats.

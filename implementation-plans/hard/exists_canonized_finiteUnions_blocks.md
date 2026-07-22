# `DensityHalesJewett.GrahamRothschild.exists_canonized_finiteUnions_blocks`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Supporting helper for the line case of the
Graham--Rothschild theorem.

## Plan

First use `FiniteUnions.bound_spec` with a `Unit` coloring to show that the selected block length
`L` is nonzero; the hypothesis `1 ≤ m` and nonemptiness of every selected block rule out `L = 0`.
This supplies a parameter line, hence a color in `C`, without assuming `[Nonempty C]`.

For each nonempty `S : Finset (Fin L)`, construct a canonical line whose variable set is exactly
`S`, fixing all other coordinates at one chosen letter of `α`. Extend the resulting support
coloring arbitrarily to the empty support. Apply `FiniteUnions.bound_spec` to obtain ordered
nonempty blocks `B`. For every nonempty index set `I` and every line `p` with variable set
`I.biUnion B`, use the canonization hypothesis to compare `p` with the canonical line selected for
that support and conclude the common-color statement.

## Verification

Keep the empty-support and nonempty-support cases explicit. Build
`DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

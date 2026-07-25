# `DensityHalesJewett.GrahamRothschild.exists_canonized_finiteUnions_blocks_of_nonempty`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Supporting helper for the line case of the
Graham--Rothschild theorem.

## Plan

For each nonempty `S : Finset (Fin L)`, construct a canonical line whose variable set is exactly
`S`, fixing all other coordinates at one chosen letter of `α`. Use the `Nonempty C` instance to
extend the resulting support coloring arbitrarily to the empty support.

Apply `FiniteUnions.bound_spec` to obtain ordered nonempty blocks `B`. For every nonempty index set
`I` and every line `p` with variable set `I.biUnion B`, compare `p` with the canonical line selected
for that support using the canonization hypothesis, and conclude the common-color statement.

## Verification

Keep construction of the canonical support line and the nonemptiness of `I.biUnion B` explicit.
Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

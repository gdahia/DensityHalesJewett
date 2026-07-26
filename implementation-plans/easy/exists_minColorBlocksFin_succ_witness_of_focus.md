# `DensityHalesJewett.FiniteUnions.exists_minColorBlocksFin_succ_witness_of_focus`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed quantifier
reduction of `minColorBlocksFin_succ_of_focus`.

## Plan

Specialize `FiniteUnions.focus` to binary words and profiles indexed by `Finset (Fin L)`, using
`Fintype.card_finset` to discharge the profile-cardinality equality. Decode the focused line into
its variable coordinates and its fixed-one stem, and apply `h` to the resulting coloring of the
last `L` coordinates.

Define the extended blocks using the variable packet and shifted old blocks. The remaining proof
is finite-set bookkeeping: prove nonemptiness from `Line.proper`, prove initial-versus-shifted
order from the two `Fin` embeddings, and split the color equation according to whether the new
index belongs to the selected union. Keep the fixed-one stem explicit in the endpoint equations;
do not rewrite an arbitrary focused endpoint as the empty subset.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

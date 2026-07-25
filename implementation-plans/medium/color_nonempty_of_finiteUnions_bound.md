# `DensityHalesJewett.GrahamRothschild.color_nonempty_of_finiteUnions_bound`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Supporting helper for the line case of the
Graham--Rothschild theorem.

## Plan

Apply `FiniteUnions.bound_spec` with a `Unit` coloring. Since `1 ≤ m`, choose one of the selected
blocks; its nonemptiness supplies a coordinate in `Fin L`. Use that coordinate to construct a
parameter line (or the diagonal line), map it through `V`, and apply `χ` to obtain an element of
`C`.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

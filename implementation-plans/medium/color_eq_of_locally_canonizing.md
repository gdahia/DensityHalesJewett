# `DensityHalesJewett.GrahamRothschild.color_eq_of_locally_canonizing`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Induct on the finite set of coordinates at which `p.idxFun` and `q.idxFun` differ. Since their
variable sets agree, every differing coordinate is fixed in both lines. At each step construct the
intermediate line obtained by replacing one fixed letter, prove its properness from the common
nonempty variable support, and apply `hlocal`.

The differing-coordinate set strictly shrinks, so the induction ends at `q`.

## Verification

Avoid a long equality chain; expose each one-coordinate replacement as the induction step. Build
`DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

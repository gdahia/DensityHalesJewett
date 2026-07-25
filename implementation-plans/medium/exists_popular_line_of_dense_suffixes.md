# `DensityHalesJewett.exists_popular_line_of_dense_suffixes`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

For every suffix with restricted slice density at least `δ / 4`, apply `hDHJ` on an embedded
`Parameters.m₀ k δ`-dimensional parameter cube. Select one complete line in each good slice, then
pigeonhole over the finite type of parameter lines.

Use the line-count bound and the definition of `Parameters.θ` to show that one selected line has a
common-suffix fiber of density at least `Parameters.θ k δ`.

## Verification

Avoid choosing lines before restricting to the finite set of dense suffixes. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

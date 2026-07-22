# `DensityHalesJewett.not_exists_sparse_correlated_fibers_certificate`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`exists_subspace_correlated_fibers` reduction.

## Plan

Embed a `Parameters.m₀ k δ`-dimensional parameter cube into the certified `M`-dimensional cube.
For every suffix word, form the family of restricted-alphabet parameter words whose images under
`W` belong to `A`. Double-count pairs of restricted parameter words and suffixes. The pointwise
fiber lower bound, together with the defining bounds on `Parameters.η`, shows that a positive
proportion of suffixes have slice density at least `δ / 4`.

For each such suffix, apply `hDHJ` at density `δ / 4` on the embedded cube. The definition of
`Parameters.m₀` supplies the required dimension inequality. Select one complete line from every
good slice and pigeonhole over the finite type of parameter lines.

Identify the relevant line count with

```text
(k + 1) ^ Parameters.m₀ k δ - k ^ Parameters.m₀ k δ
```

using the line/subspace equivalence already developed in `Subspace`. The pigeonhole lower bound
and the definition of `Parameters.θ` then produce one line whose common-suffix fiber has density at
least `Parameters.θ k δ`, contradicting the strict upper bound in the sparse certificate.

## Verification

Separate the double-counting identity, the dense-suffix threshold estimate, and the finite-line
cardinality calculation. Avoid choosing lines before restricting to the finite set of good
suffixes. Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all
non-`sorry` diagnostics.

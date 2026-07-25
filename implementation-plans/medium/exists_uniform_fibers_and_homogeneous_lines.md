# `DensityHalesJewett.exists_uniform_fibers_and_homogeneous_lines`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Apply `Subspace.exists_fibers_dense` with error `Parameters.η k δ ^ 2 / 2`. Color a parameter-cube
line good when the common suffix fiber of its first `k` points has density at least
`Parameters.θ k δ`, and apply `GrahamRothschild.lines_twoColor`.

Compose the homogeneous parameter subspace with the uniform-fiber subspace. Prove the two
evaluation identities needed to transport the pointwise fiber lower bound and the line coloring.
Return the resulting all-good or all-sparse alternative.

## Verification

Keep the two composition identities explicit. Build `DensityHalesJewett.DensityIncrement` with
normal heartbeats and resolve all non-`sorry` diagnostics.

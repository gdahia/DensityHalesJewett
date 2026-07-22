# `DensityHalesJewett.exists_correlated_fibers_or_sparse_certificate`

Source: `DensityHalesJewett/DensityIncrement.lean`. Extracted from the completed
`exists_subspace_correlated_fibers` reduction.

## Bound construction

Let the homogeneous working dimension be at least both the requested output dimension `m` and
`Parameters.m₀ k δ`. Choose a larger parameter dimension sufficient first for
`Subspace.exists_fibers_dense` with error `Parameters.η k δ ^ 2 / 2`, and then for
`GrahamRothschild.lines_twoColor` with that working dimension. Connect this eventual statement to
`correlatedFibersBound`; if the bound remains opaque while developing the proof, expose a separate
sufficiency theorem and use only that theorem here.

## Plan

Apply `Subspace.exists_fibers_dense` to obtain a large `(k+1)`-alphabet subspace above every point
of which the suffix fiber has density at least `δ - η²/2`. Color a parameter-cube line good when
the suffixes on which all of its first `k` points belong to `A` have density at least `θ`.

Apply `GrahamRothschild.lines_twoColor` to make this coloring constant on a working subspace.
Compose the working subspace with the uniform-fiber subspace and prove the two evaluation
identities needed to transport both the pointwise fiber bound and the line coloring.

In the good case, restrict the working parameter cube to its first `m` directions and return the
left disjunct. In the bad case, retain the whole working subspace, its lower bound
`Parameters.m₀ k δ ≤ M`, the pointwise fiber estimates, and the strict line-density upper bounds as
the sparse certificate in the right disjunct.

## Verification

Keep bound selection, composition identities, and the good/bad split as separate phases. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve every non-`sorry`
diagnostic attributed to the module.

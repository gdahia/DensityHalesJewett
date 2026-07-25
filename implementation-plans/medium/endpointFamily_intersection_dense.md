# `DensityHalesJewett.endpointFamily_intersection_dense`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Extend every complete restricted-alphabet parameter line uniquely by assigning the final alphabet
letter on its variable set. Show that all replacements of this endpoint lie in `A`, so the endpoint
belongs to `intersection (endpointFamily A V)`.

Prove the endpoint map injective using the parameter-line encoding, then combine the assumed
line-density lower bound with the line/subspace cardinality identity to obtain intersection density
at least `Parameters.θ k δ / 4`.

## Verification

Keep endpoint injectivity and the cardinality calculation separate. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

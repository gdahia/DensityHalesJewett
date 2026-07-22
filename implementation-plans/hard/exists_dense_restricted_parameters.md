# `DensityHalesJewett.Subspace.exists_dense_restricted_parameters`

Source: `DensityHalesJewett/UniformFibers.lean`. Extracted from the restricted-alphabet subspace
argument.

## Plan

Apply `exists_fibers_dense` with error `δ / 2` to obtain an `M`-subspace `W`. The ambient density
bound and `δ ≤ 1` verify the strict hypotheses and show that every fiber over `W` has density at
least `δ / 2`, hence so does every fiber over a parameter word restricted along
`Fin.castSuccEmb`.

Double-count the pairs `(x, y)` for which `concat (W (Fin.castSucc ∘ x)) y ∈ A`. Averaging first
over restricted parameter words and then over suffixes gives a suffix `y` whose corresponding
parameter family has density at least `δ / 2`.

## Verification

Keep the density conversions separate from the double-counting identity, use the existing fiber
average API, and build `DensityHalesJewett.UniformFibers` without non-`sorry` warnings.

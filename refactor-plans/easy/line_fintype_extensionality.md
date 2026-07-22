# Reuse line extensionality and the existing line fintype

Sources: `DensityHalesJewett/UniformFibers.lean` (`card_line_le`, `lineFintype`) and
`DensityHalesJewett/DensityIncrement.lean` (`exists_large_insensitive_intersection`).

## Finding

The injectivity of `fun l ↦ l.idxFun` is proved twice by destructing both line structures. Mathlib's
`Combinatorics.Line.ext` proves this directly. A third copy is used to manufacture a local
`Fintype` in `DensityIncrement`, even though `Subspace.lineFintype` is already available from
`UniformFibers`.

## Plan

- Pass `Combinatorics.Line.ext` directly to `Fintype.card_le_of_injective` in `card_line_le`.
- Pass it directly to `Fintype.ofInjective` in `lineFintype`.
- In `exists_large_insensitive_intersection`, replace the repeated `Fintype.ofInjective`
  construction with `letI := Subspace.lineFintype k m`.

This removes non-idiomatic proof lambdas and consolidates the instance construction without adding
another helper.

## Verification

Build `DensityHalesJewett.UniformFibers` and `DensityHalesJewett.DensityIncrement`.


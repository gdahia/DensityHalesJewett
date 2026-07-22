# `DensityHalesJewett.Subspace.fixSuffixReindex_statistics`

Source: `DensityHalesJewett/DensityIncrement.lean`. Coordinate-transport helper for “Many lines
in a dense slice.”

## Plan

First prove the evaluation identity

```text
fixSuffixReindex e V y x = concat (V x) y ∘ e.symm.
```

For relative density, unfold `Subspace.relativeDensity` and `suffixPullback`, rewrite evaluation by
that identity, and use `Finset.mem_map_equiv`. Repeat pointwise inside the line filter for the
second equality, then unfold `suffixLines`.

## Verification

Use `funext` only for the evaluation identity and keep both filter equalities extensional. Build
`DensityHalesJewett.DensityIncrement`.

# `DensityHalesJewett.density_increment`

Source: `DensityHalesJewett/DensityIncrement.lean`. Blueprint: “Density increment or a line.”

## Bound construction

First prove the eventual dichotomy under `HasDensityHJ k`, choosing every intermediate dimension
from the structured-correlation, Graham--Rothschild, and intersection-tiling specifications. Define
`incrementBound k d δ` by conditional `Nat.find` on `HasDensityHJ k`, with a separate
`incrementBound_spec` theorem.

## Plan

Split on `IsLineFree A`. If false, unpack its negation into a complete line and return the first
alternative. Otherwise apply `exists_structured_correlation` at a working dimension large enough to
support a `k`-fold tiling by `d`-subspaces. Obtain an insensitive intersection `D` of density at
least `γ` and enhanced `A`-density.

Choose `β = γ²/(4*k)` and tile all but at most `γ²/2` of `D` using
`exists_disjoint_subspaces_iInter`. Let `T` be the union of tile ranges. Prove the real inequality

```text
dens(A ∩ T) ≥ (δ + γ/2) * dens(T)
```

from the correlation on `D`, the uncovered error, `dens D ≥ γ`, and `T ⊆ D`. Express densities of
`T` and `A∩T` as sums over pairwise-disjoint tiles. Finite averaging then yields one tile with the
desired relative density; compose it with the outer working subspace.

## Verification

Isolate the real-arithmetic and disjoint-average lemmas. Build with normal heartbeats only.

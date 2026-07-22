# `DensityHalesJewett.exists_mem_inter_of_large_density`

Source: `DensityHalesJewett/DensityIncrement.lean`. Finite-density helper for “Many lines in a
dense slice.”

## Plan

Assume `S ∩ T` is empty. Use `card_union_of_disjoint` (or the corresponding density lemma) to
deduce `dens S + dens T ≤ 1`. The two lower bounds instead give
`1-η + θ/2 ≤ dens S + dens T`, contradicting `η < θ/2`. Extract an element of the nonempty
intersection and split its membership into the requested pair.

## Verification

Handle the empty ambient type directly if the density API does not simplify it automatically.
Build `DensityHalesJewett.DensityIncrement`.

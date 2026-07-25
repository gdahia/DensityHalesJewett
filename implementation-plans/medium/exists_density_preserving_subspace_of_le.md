# `DensityHalesJewett.exists_density_preserving_subspace_of_le`

Source: `DensityHalesJewett/Main.lean`.

## Plan

Split `Fin n` into the first `m` coordinates and a suffix using `m ≤ n`. Average the densities of
the corresponding `m`-dimensional coordinate fibers over all fixed suffixes. Since their average
is `dens A`, select one suffix with fiber density at least the ambient density and package it as a
subspace.

## Verification

Build `DensityHalesJewett.Main` with normal heartbeats and resolve all non-`sorry` diagnostics.

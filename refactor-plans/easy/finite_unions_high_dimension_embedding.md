# Use the canonical finite-coordinate embedding

Source: `DensityHalesJewett/GrahamRothschild.lean`, declaration
`FiniteUnions.exists_mono_in_high_dimension`.

## Finding

`exists_mono_in_high_dimension` manually constructs the canonical embedding `Fin L ↪ Fin n`.
Mathlib already provides exactly this map as `Fin.castLEEmb hn`.

## Plan

Define `e := Fin.castLEEmb hn`, or use it directly if that keeps the map expressions readable.
Remove the handwritten `toFun` and `inj'` fields. Simplify the subsequent `Finset.map` membership
and order arguments with the `Fin.castLEEmb` API.

## Verification

Build `DensityHalesJewett.GrahamRothschild` and check that no new simplifier or unused-declaration
warnings appear.

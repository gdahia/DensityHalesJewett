# Small finite-unions proof cleanup

Source: `DensityHalesJewett/GrahamRothschild.lean`, declarations `BlockWord.select_eq_one` and
`FiniteUnions.exists_mono_in_high_dimension`.

## Findings

1. `select_eq_one` places both the `if_neg` proof and an arithmetic proof inside a long `rw` list,
   contrary to rules 7 and 13.
2. `exists_mono_in_high_dimension` manually constructs the canonical embedding `Fin L ↪ Fin n`.
   Mathlib already provides exactly this map as `Fin.castLEEmb hn`.

## Plan

For `select_eq_one`, rewrite `select`, expose the conditional and induction premises as ordinary
subgoals, and solve them in argument order. Keep the recursive call as the main closing step.

For `exists_mono_in_high_dimension`, define `e := Fin.castLEEmb hn`, or use it directly if that
keeps the map expressions readable. Remove the handwritten `toFun` and `inj'` fields. Simplify the
subsequent `Finset.map` membership and order arguments with the `Fin.castLEEmb` API.

## Verification

Build `DensityHalesJewett.GrahamRothschild` and check that no new simplifier or unused-declaration
warnings appear.


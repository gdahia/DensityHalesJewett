# Lean refactoring plans

This directory records proof refactors found by auditing the repository against `AGENTS.md`.
It intentionally contains plans only: no Lean declaration has been changed.

The audit covered every completed proof in `DensityHalesJewett/*.lean`. Declarations ending in
`sorry` are excluded because they are already tracked in `implementation-plans/`. `Basic.lean` has
no proofs, and the completed portions of `Insensitive.lean` and `Subspace.lean` had no material
finding worth a separate plan.

## Difficulty

- `easy/`: local rewrites or direct theorem substitutions with little downstream impact.
- `medium/`: a whole proof should be reorganized, or a library substitution affects several
  neighboring declarations.
- `hard/`: coordinate-heavy proofs where a style refactor is likely to require substantial
  elaboration work even though the mathematics is unchanged.

## Inventory

- `easy/`: 6 plans
- `medium/`: 4 plans
- `hard/`: 1 plan

Within a difficulty level, use source dependency order: `Word`, `Subspace`,
`GrahamRothschild`, `UniformFibers`, `Insensitive`, `DensityIncrement`, `Main`, then `Szemeredi`.

## Confirmed library substitutions

- Replace the hand-built `Fin L ↪ Fin n` in
  `FiniteUnions.exists_mono_in_high_dimension` with `Fin.castLEEmb`.
- Use `Combinatorics.Line.ext` for injectivity of `Line.idxFun`, and reuse
  `Subspace.lineFintype` instead of rebuilding the same instance in `DensityIncrement`.
- Replace the local `BlockWord := List ℕ` monoid and its `toList` API with mathlib's
  `FreeMonoid ℕ`, `FreeMonoid.toList_one`, and `FreeMonoid.toList_mul`.

## Verification policy

For every executed plan, build the affected module with `lake build`, inspect the complete output,
and resolve all warnings and associated `info:` messages attributed to that module. Do not raise
the heartbeat limit.


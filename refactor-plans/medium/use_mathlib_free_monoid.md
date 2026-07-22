# Replace the local block-word monoid with `FreeMonoid`

Source: `DensityHalesJewett/GrahamRothschild.lean`, namespace `BlockWord` and its uses in
`exists_infinite_mono`.

## Finding

The local `BlockWord := List ℕ` layer recreates the free monoid on `ℕ`, including its monoid
instance, identity `toList`, and the lemmas `toList_one` and `toList_mul`. Mathlib provides these as
`FreeMonoid ℕ`, `FreeMonoid.toList`, `FreeMonoid.toList_one`, and
`FreeMonoid.toList_mul` in `Mathlib.Algebra.FreeMonoid.Basic`.

## Plan

Import the free-monoid module and replace `BlockWord` with `FreeMonoid ℕ` (an abbreviation is
acceptable if retaining the domain name improves readability). Delete the local monoid instance,
`toList`, `toList_one`, and `toList_mul`.

Construct singleton words with `FreeMonoid.of`. Update `singletonStream`, `select`,
`mem_fp_singletonStream`, `mem_toFinset_select`, and `exists_infinite_mono` to use the mathlib
conversion and simp lemmas. Keep the project-specific selection and ordered-support lemmas; they
are not present in mathlib.

Pay special attention to elaboration of list literals and to the `Hindman.FP` multiplication
lemmas, since the type synonym currently hides those coercion details.

## Verification

Build `DensityHalesJewett.GrahamRothschild`. Inspect the full linter output for namespace and simp
normal-form suggestions.


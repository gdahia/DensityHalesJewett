# Expose the chosen-line specification

Source: `DensityHalesJewett/UniformFibers.lean`, declaration `exists_common_dense_line`.

## Finding

The proof constructs `lineAt` with a substantial `Classical.choose` expression containing two
inline proofs, then repeats the entire existence theorem inside `Classical.choose_spec`. It also
introduces a one-use equality `hfl` solely to rewrite the selected line. This conflicts with rules
2, 7, and 9 and makes elaboration errors hard to localize.

## Plan

After proving `B.Nonempty`, define the chosen line on `{x // x ∈ B}` and immediately state a
`lineAt_spec` fact giving all of its points in `A`. This is a justified named fact because it is the
API of the local choice and separates choice from counting.

Define the total coloring `f` from `lineAt` and the fallback line. Apply `exists_fiber_density`
immediately. In the final inclusion proof, normalize membership in the fiber of `f`, rewrite the
dependent `if` once, and apply `lineAt_spec` directly. Avoid rebuilding the existential proof or
placing its premises inline in `choose_spec`.

## Verification

Build `DensityHalesJewett.UniformFibers`.


# Refactor the multidimensional density induction

Source: `DensityHalesJewett/UniformFibers.lean`, declaration `exists_eventually_of_density`.

## Finding

The inductive step is mathematically well phased, but its final containment proof accumulates
one-use coordinate facts (`hxC`, `hx`, and `hz`) and a substantial coordinate equality solely to
rewrite the next goal. This is the main completed proof where rules 2, 3, 9, and 13 suggest a
structural refactor rather than isolated edits.

## Plan

Keep the meaningful dimension choices `q`, `p`, the transport equivalence, and the dense prefix
family named. Apply the induction hypothesis and construct `W` as now.

For containment, normalize membership in `C` immediately after applying `hV x`, specialize the
result at the selected letter, and transport membership through `Finset.mem_map_equiv`. Use
`convert` on that transported membership as the main closing theorem. Solve its remaining
pointwise equality by cases on the sum coordinate, using `Fin.eq_zero` only in the `Fin 1` branch.
Do not manufacture the whole function equality `hz` as a one-use rewrite rule.

If elaboration requires a named coordinate lemma, state it as a reusable simp lemma for the
constructed concatenated subspace rather than as a local equality used once. Do not alter the
dimension bound or increase heartbeats.

## Verification

Build `DensityHalesJewett.UniformFibers` and inspect the full Lake linter output. Because this proof
feeds the bound specifications downstream, also build the top-level `DensityHalesJewett` target.


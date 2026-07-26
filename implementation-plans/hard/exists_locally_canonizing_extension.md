# `DensityHalesJewett.GrahamRothschild.exists_locally_canonizing_extension`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Feasibility audit

The deleted `exists_locally_canonizing_profile_extension` had exactly the same hypotheses and
conclusion as this declaration, so it was only a rename, not a reduction. The theorem itself is a
finite Graham--Rothschild/canonization statement and is mathematically valid, but one application
of `FiniteUnions.focus` is insufficient: the ambient coloring must be stabilized simultaneously
for every old parameter-line context and every fixed/variable status of the new parameter.

## Detailed construction

Fix the old witness dimension `N`.

1. Enumerate the finite set
   `P := Combinatorics.Line (Fin alphabet) (Fin blocks)` of old parameter-line contexts and the
   finite set of one-coordinate line statuses `Option (Fin alphabet)`. A profile is the function
   which assigns to every compatible pair `(p,t)` the color of the ambient line obtained by
   inserting status `t` after `p`.
2. Choose a fresh packet dimension by the multidimensional Hales--Jewett theorem with color type
   equal to this complete finite profile. Focusing a packet produces a new parameter direction
   on which all entries of the profile are constant; retaining the complete function-valued
   color is essential.
3. For each fixed choice on the fresh packet, pull `χ` back to a coloring of lines on `Fin N` and
   apply `hN`. Because there are finitely many packet profiles, iterate this operation, nesting
   the returned old-coordinate subspaces. The induction invariant must record a single old
   subspace which works for every profile already processed; choosing unrelated subspaces for
   different profiles is not enough.
4. Concatenate that nested old subspace with the focused fresh direction, then reindex the
   coordinate sum to `Fin M`. Prove `Subspace.mapLine` compatibility before unfolding
   `IsLocallyCanonizing`.
5. Given lines `p q` on `Fin (blocks + 1)`, obtain the exceptional coordinate `i`. Split it using
   `Fin.lastCases`.
   - In an old-coordinate branch, remove the last status and invoke local canonization of the
     nested old subspace for the corresponding retained profile.
   - In the last-coordinate branch, the old contexts agree and the complete focused profile gives
     the color equality directly.

## Required helper statements

- a `Fintype` instance and cardinal bound for the finite line-context profile;
- an iterated-focus lemma for a finite list of function-valued colorings, whose invariant returns
  one nested subspace satisfying every processed profile;
- `mapLine` lemmas for concatenation and reindexing;
- variable-set formulas for deleting or adjoining the last parameter coordinate;
- the two `Fin.lastCases` branches of local canonization.

Each helper must expose its actual profile compatibility invariant. A helper with the same final
existential conclusion is not an acceptable reduction.

## Verification

Build `DensityHalesJewett.GrahamRothschild` at normal heartbeats after each phase. This plan is
hard, not easy, until the iterated-focus invariant and the `mapLine`/`variableSet` transport
helpers exist.

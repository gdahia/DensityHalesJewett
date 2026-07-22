# `DensityHalesJewett.GrahamRothschild.canonize`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Blueprint: “Block canonization.”

## Bound construction

Prove an existential block-length theorem by reverse finite recursion. Every step invokes the
choice-based coloring Hales--Jewett bound for a finite profile type. Let the total selected length be
`M`; pad from `M` to any `n ≥ M`. Define `canonizationBound` with `Nat.find` from this eventual
statement and expose `canonizationBound_spec`.

## Plan

Represent `n` coordinates as an ordered sum of `L` blocks. Select a line word in each block in
reverse order. At block `i`, color each constant block word by the complete profile obtained by
varying:

- all fixed words in earlier blocks;
- fixed-letter-or-variable choices in already selected later blocks;
- a dummy value for contexts containing no variable.

Hales--Jewett makes this profile constant along a selected line. Assemble the selected block lines
into an `L`-direction subspace `V`.

For lines `p,q` with equal `variableSet`, compare their fixed letters one block at a time. At every
changed block some variable block remains, so the corresponding stored profile equality applies.
Chain these equalities by induction on the finite set of differing blocks; avoid a long `calc`.

## Supporting API and verification

Introduce finite encodings for profile types, block sum equivalences, and evaluation lemmas for the
assembled subspace. Prove padding separately. Build with Lake and watch heartbeat usage; refactor
rather than increasing it.

# `DensityHalesJewett.FiniteUnions.minColorBlocksFin_succ_of_focus`

Source: `DensityHalesJewett/GrahamRothschild.lean`. Extracted from the completed reduction of
`exists_minColor_blocks_fin_step`.

## Plan

Use `Finset (Fin L)` as the finite profile type, whose cardinality is `2 ^ L`. A binary word on
the first `n` coordinates records a subset of that packet. For every old subset `U`, color the
word by the original color of its selected initial coordinates together with the shifted copy of
`U`.

Apply `FiniteUnions.focus` using `hn`. The variable coordinates of the focused binary line form
the new block, and its fixed-one coordinates form a stem. Apply `h` to the coloring of old subsets
with that stem inserted.

Index the new block by `0` and the shifted old blocks by successors. For a nonempty union, split
on membership of `0`. If `0` is present, the focusing equality removes the new block and gives
the new minimum color; otherwise, transport the union and its minimum through `Fin.succ`.
Initial-versus-shifted coordinate order proves strict block separation.

## Verification

Build `DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics attributed to the helper.

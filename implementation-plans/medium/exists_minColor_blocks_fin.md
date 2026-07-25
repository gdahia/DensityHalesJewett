# `DensityHalesJewett.FiniteUnions.exists_minColor_blocks_fin`

Source: `DensityHalesJewett/GrahamRothschild.lean`.

## Plan

Proceed by reverse finite recursion on the `s` selected blocks. At each stage, split a sufficiently
large unused final interval into equal packets. A word records the allowed choice in each packet;
its color is the full finite profile over unions of blocks already selected.

Apply `FiniteUnions.focus` to make that profile constant on a line. Use the variable packets as the
next nonempty block and absorb fixed packets into the carried stem. The stored profile equality
shows that every nonempty union has the color assigned to its least selected block.

## Verification

Keep packet indexing and the profile evaluation identity explicit. Build
`DensityHalesJewett.GrahamRothschild` with normal heartbeats and resolve all non-`sorry`
diagnostics.

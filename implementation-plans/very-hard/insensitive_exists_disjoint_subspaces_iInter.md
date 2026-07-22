# `DensityHalesJewett.IsInsensitive.exists_disjoint_subspaces_iInter`

Source: `DensityHalesJewett/Insensitive.lean`. Blueprint: “Tiling an intersection.”

## Bound construction

Define `intersectionTilingBound` by choice from an induction on `r`; the selected threshold may
iterate `tilingBound` very wastefully. Provide a specification theorem for all larger `n`.

## Plan

Induct on `r`. For `r=1`, identify `intersection D` with `D 0` and apply
`exists_disjoint_subspaces`. For the successor step, first tile the intersection of the initial `r`
families by pairwise disjoint large-dimensional subspaces. Pull the last insensitive family back to
each tile's parameter cube; prove pullback preserves the corresponding insensitivity.

On a large tile, either the pulled-back last family has density below `2β`, in which case discard
its contribution, or apply the one-family tiling theorem inside it to obtain `m`-subspaces. Compose
the inner subspaces with the outer tile.

Flatten all inner families. Prove global pairwise disjointness by splitting whether two inner tiles
have the same outer parent. Containment follows from containment in the initial intersection and
the last family. Bound the final uncovered part by the disjoint sum of the first-stage error and at
most `2β` inside all outer tiles, yielding `< 2*(r+1)*β`.

## Verification

Establish density-summing lemmas for finite pairwise-disjoint ranges before the induction. Build
the module with all generated subgoals bulleted explicitly.

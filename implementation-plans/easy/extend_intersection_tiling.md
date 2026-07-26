# `DensityHalesJewett.IsInsensitive.extend_intersection_tiling`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Apply the outer intersection tiling to the first `r` families.  On every outer tile, pull back the
last family.  Use `hinner` on pullbacks of density at least `2 * β`; retain no inner tiles on the
remaining parents.  Flatten the composed families with `composed_inner_tiles_facts`.

Different outer parents are disjoint.  The uncovered part is contained in the union of the outer
uncovered set, the sparse pullbacks, and the inner uncovered sets.  Sum their normalized
densities to obtain `2 * r * β + 2 * β = 2 * (r + 1) * β`.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

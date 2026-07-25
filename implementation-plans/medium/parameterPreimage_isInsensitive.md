# `DensityHalesJewett.IsInsensitive.parameterPreimage_isInsensitive`

Source: `DensityHalesJewett/Insensitive.lean`.

## Plan

Unfold `parameterPreimage`. If two parameter words are insensitive-equivalent for `a,b`, evaluate
them through `V`. At variable coordinates the evaluations remain insensitive-equivalent, while
fixed coordinates agree exactly. Apply `hD` to conclude equivalent membership.

## Verification

Build `DensityHalesJewett.Insensitive` with normal heartbeats and resolve all non-`sorry`
diagnostics.

# `DensityHalesJewett.Parameters.θ_le_one`

Source: `DensityHalesJewett/DensityIncrement.lean`. Numerical helper for “Many lines in a dense
slice.”

## Plan

Unfold `θ`. The denominator is positive by `θ_denominator_pos`. Since `m₀` is positive and
`k+1 > k`, prove the difference of powers is at least one; then use `δ ≤ 1` to bound the numerator
`δ/4` by one. Apply `div_le_one` or cross-multiply by the positive denominator.

## Verification

Make all natural-to-real casts explicit enough for `norm_num`/`positivity`; do not add heartbeat
options. Build `DensityHalesJewett.DensityIncrement`.

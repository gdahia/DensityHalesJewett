# `DensityHalesJewett.dense_suffixes_of_uniform_fibers`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Double-count restricted parameter words and suffixes. Average the pointwise fiber lower bounds,
then use a threshold estimate to show that suffixes whose restricted parameter slice has density
at least `δ / 4` themselves have density at least `δ / 4`. The defining upper bound on
`Parameters.η` supplies the numerical slack.

## Verification

Keep the double-counting identity separate from the real inequality. Build
`DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

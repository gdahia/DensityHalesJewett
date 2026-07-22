# `DensityHalesJewett.average_suffixPullback_lower`

Source: `DensityHalesJewett/DensityIncrement.lean`. Supporting helper for “Many lines in a dense
slice.”

## Plan

Expand `suffixPullback` and both densities as normalized indicator sums. Swap the two finite
averages over parameter words and suffix words, then identify the inner suffix average with the
density of `fiber A (V x)`. Apply the pointwise hypothesis with `Finset.expect_le_expect` and
simplify the expectation of the constant lower bound.

## Verification

Keep the statement generic in all four types. Build `DensityHalesJewett.DensityIncrement` and
resolve every non-`sorry` warning.

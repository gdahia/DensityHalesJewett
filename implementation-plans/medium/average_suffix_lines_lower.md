# `DensityHalesJewett.average_suffixLines_lower`

Source: `DensityHalesJewett/DensityIncrement.lean`. Supporting helper for “Many lines in a dense
slice.”

## Plan

Expand `suffixLines` and densities into indicator expectations. Use the finite Fubini identity to
swap the average over parameter lines with the average over suffix words. For each line, the inner
suffix density is exactly the expression bounded by `hV`. Average `hV` and simplify the constant
expectation.

## Verification

Avoid enumerating line structures explicitly; the supplied `Fintype` is sufficient. Build
`DensityHalesJewett.DensityIncrement`.

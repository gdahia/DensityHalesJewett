# `DensityHalesJewett.endpointFamily_isInsensitive`

Source: `DensityHalesJewett/DensityIncrement.lean`.

## Plan

Unfold `endpointFamily`, `replaceLastLetter`, `IsInsensitive`, and `InsensitiveEquiv`. If two words
differ only by freely interchanging `i.castSucc` and `Fin.last k`, replacing both letters by
`i.castSucc` produces the same word, so membership is equivalent.

## Verification

Build `DensityHalesJewett.DensityIncrement` with normal heartbeats and resolve all non-`sorry`
diagnostics.

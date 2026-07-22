# `DensityHalesJewett.Subspace.extend_restricted_subspace`

Source: `DensityHalesJewett/UniformFibers.lean`. Extracted from the restricted-alphabet subspace
argument.

## Plan

Lift `S`, whose constants and variable letters lie in `Fin k`, to a subspace over `Fin (k+1)`:
map constant letters with `Fin.castSuccEmb` and retain the same parameter directions. Compose the
lifted subspace with `W`, attach the fixed suffix `y`, and transport ambient coordinates along
`e`.

Prove the evaluation identity on parameter words restricted along `Fin.castSuccEmb`. Unfold
`restrictAlphabet`, take an arbitrary member of its image, rewrite it using that identity, and
close with `hS`.

## Verification

Expose any reusable alphabet-lifting definition and evaluation lemma in `Subspace.lean` if that
makes the proof shorter. Build `DensityHalesJewett.UniformFibers` and resolve all non-`sorry`
warnings attributed to the module.

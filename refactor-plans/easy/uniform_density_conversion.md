# Linearize cardinal-density conversions

Source: `DensityHalesJewett/UniformFibers.lean`, declarations `density_le_of_card_le` and
`card_le_of_density_le`.

## Finding

`card_le_of_density_le` names denominator positivity and the result of `le_div_iff₀`, then uses each
fact once. These facts merely feed the next theorem application, which is the pattern prohibited by
rules 3 and 9. The reverse conversion is already closer to the preferred style.

## Plan

Normalize with `Finset.nnratCast_dens` first. Apply `le_div_iff₀` or its converse immediately,
exposing denominator positivity as the first bullet and the converted cardinal inequality as the
second. Finish by `simpa only` with `Fintype.card_pi_const`, `Fintype.card_fin`, and `Nat.cast_pow`.

Keep both domain-specific conversion lemmas: mathlib supplies the density formula but not these
project-specific real-valued inequality interfaces.

## Verification

Build `DensityHalesJewett.UniformFibers`.


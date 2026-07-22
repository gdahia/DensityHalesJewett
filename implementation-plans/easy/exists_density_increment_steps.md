# `DensityHalesJewett.exists_density_increment_steps`

Source: `DensityHalesJewett/Main.lean`. Extracted from the completed reduction of
`density_hales_jewett_fin`.

## Plan

Use `Parameters.γ_pos hk hδ` to show that `Parameters.γ k δ / 2` is positive. Apply the
Archimedean property to choose a natural number `R` strictly larger than
`(1 - δ) / (Parameters.γ k δ / 2)`, then rearrange the resulting inequality to obtain

```text
1 < δ + R * (Parameters.γ k δ / 2).
```

## Verification

Keep the cast of `R` explicit and let `linarith` perform only the final rearrangement. Build
`DensityHalesJewett.Main` and resolve every non-`sorry` diagnostic attributed to the module.

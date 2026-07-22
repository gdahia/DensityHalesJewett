# Remove automation-only facts from density estimates

Source: `DensityHalesJewett/DensityIncrement.lean`, declarations `density_near_average` and
`density_complement_bounds`.

## Finding

`density_near_average` introduces `h_dens_H_lt`, `h_pos`, `hx_lt`, and `h_upper_bound` only so that
later `linarith`/`nlinarith` calls can discover them in the local context. In
`density_complement_bounds`, the partition identities `hsplitA` and `hsplitC` are likewise used
only implicitly by automation. These are direct violations of rule 9. The expectation-algebra
`calc` in `density_near_average` is also more mechanical than mathematical.

## Plan

In `density_near_average`, normalize indicator branches first. Pass the strict density bound,
coefficient positivity, and pointwise upper bounds explicitly to the arithmetic tactic that needs
them. Rewrite the expected affine indicator using `Finset.expect_add_distrib`,
`Finset.mul_expect`, and `Finset.expect_indicator_one` in a linear sequence instead of naming an
equality that is immediately rewritten.

In `density_complement_bounds`, pass typed proofs of `Finset.dens_inter_add_dens_sdiff` and
`Finset.dens_sdiff_add_dens_eq_dens` directly to `linarith`/`nlinarith` after the required casts and
normalizations. Retain `houtside` only if it remains genuinely reused in both conjuncts.

## Verification

Build `DensityHalesJewett.DensityIncrement` and ensure arithmetic automation remains comfortably
within the existing heartbeat limit.


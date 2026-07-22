# Linearize elementary density threshold helpers

Source: `DensityHalesJewett/DensityIncrement.lean`, declarations `density_half_threshold`,
`exists_mem_inter_of_large_density`, and `Parameters.θ_le_one`.

## Finding

These short arithmetic proofs accumulate several one-use facts. In
`exists_mem_inter_of_large_density`, the union-density equality and density upper bound are used
only implicitly by `linarith`, an explicit rule 9 violation. `density_half_threshold` similarly
names a numerator rewrite and two comparison steps used once.

## Plan

- In `density_half_threshold`, apply `density_ge_threshold` immediately, normalize
  `θ - θ / 2` with `ring_nf` or `ring`, and prove the remaining comparison as a single ordered-field
  subgoal.
- In `exists_mem_inter_of_large_density`, derive `Disjoint S T` directly from the negated witness.
  Supply `Finset.dens_union_of_disjoint` and `Finset.dens_le_one` explicitly to the final arithmetic
  tactic instead of storing automation-only facts.
- In `Parameters.θ_le_one`, apply `div_le_one` immediately. Supply denominator positivity directly
  and prove the lower bound using `power_difference_mono` without the one-use `hm₀_pos`,
  `h_one_le_diff`, and `h1` chain where elaboration permits.

## Verification

Build `DensityHalesJewett.DensityIncrement`.


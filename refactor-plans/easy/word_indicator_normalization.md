# Normalize indicator proofs in `Word`

Source: `DensityHalesJewett/Word.lean`, especially `average_density_fiber` and
`density_ge_threshold`.

## Finding

Several `rw` calls pass freshly constructed membership proofs to
`Set.indicator_of_mem` or `Set.indicator_of_notMem`. The proofs are small, but this repeats the same
membership normalization and leaves proof terms embedded in rewrite commands. This is an
opportunity to follow rules 1, 7, and 13 more directly.

## Plan

After each membership `by_cases`, normalize `fiber`, `H`, and `concat` once. Let `simp only` close
the matching indicator and `Pi.one_apply` goals from the branch hypothesis. Avoid introducing
named membership facts unless they are reused.

Keep the main mathematical structure of both proofs unchanged. In particular, retain the early
application of `Finset.expect_equiv` and `Finset.expect_le_expect`.

## Verification

Build `DensityHalesJewett.Word` and require warning-free output for this file.


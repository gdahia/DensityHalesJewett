# Streamline the two expectation double-counting proofs

Source: `DensityHalesJewett/DensityIncrement.lean`, declarations
`average_suffixPullback_lower` and `average_suffixLines_lower`.

## Finding

Both proofs implement the same finite Fubini pattern: express density as an expected indicator,
commute two expectations with `Finset.expect_comm`, identify the pointwise predicates, and apply a
lower bound. Their `calc` blocks communicate a genuine mathematical chain and are permitted by
rule 8, but the pointwise identification currently creates branch-local membership facts that are
used once, and the final expectation lower bound is stored only to be composed once.

## Plan

Keep the Fubini chain visible. In each pointwise predicate step, unfold the relevant filter once and
let `simp only` use the branch hypothesis directly, avoiding `hy`/`hx` membership intermediates.

After proving the expectation identity, rewrite the target by that identity and apply
`Finset.le_expect` immediately. Alternatively, reverse the identity if that makes the final `rw`
linear. Do not factor out a new generic helper unless both completed proofs become materially
shorter and its statement is mathematically natural.

## Verification

Build `DensityHalesJewett.DensityIncrement`.


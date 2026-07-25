# Clean up local rewrites in `Main`

Source: `DensityHalesJewett/Main.lean`, declarations `binarySupport_injective` and
`middleBinomial_ratio_le_central`.

## Finding

`binarySupport_injective` names an equivalence used only through the context by `grind`, which is
the exact anti-pattern in rule 9. `middleBinomial_ratio_le_central` uses `show ... by` terms and
tactic-generated equalities inside `rw` lists, contrary to rules 12 and 13; its two division facts
are also one-use rewrite equalities.

## Plan

For `binarySupport_injective`, normalize equality of supports pointwise and pass the resulting
equivalence explicitly to `grind`, or finish each `Fin 2` case directly.

For `middleBinomial_ratio_le_central`, normalize parity division with `norm_num`/`omega` at the goal
rather than naming `hdiv`. Prove the power identity by direct normalization (`norm_num`, `ring_nf`,
or `norm_num [← pow_mul]`) before the main inequality, never as a `show ... by` entry in an `rw`
list. Preserve `hchoose`, since it is the meaningful combinatorial estimate in the odd case.

## Verification

Build `DensityHalesJewett.Main`.


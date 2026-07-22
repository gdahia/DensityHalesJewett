# `DensityHalesJewett.exists_density_increment_schedule`

Source: `DensityHalesJewett/Main.lean`. Extracted from the completed reduction of
`density_hales_jewett_fin`.

## Plan

Construct `d` backwards from stage `R`. Set `d R = 1`; for each earlier `j`, set `d j` to the
maximum of `1` and

```text
incrementBound k (d (j + 1)) (δ + j * (Parameters.γ k δ / 2)).
```

A convenient implementation is a finite reverse recursion or a forward recursion defining the
reversed schedule, followed by reindexing with `R - j`. Prove separately that the endpoint is one,
that every scheduled dimension is positive, and that each density-increment bound is below the
preceding dimension.

## Verification

Keep the natural-number reindexing arithmetic isolated from the real-valued density expression.
Build `DensityHalesJewett.Main` without increasing heartbeats and resolve every non-`sorry`
diagnostic attributed to the module.

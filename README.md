# DensityHalesJewett

This repository contains the Lean 4 formalization of
[**A Simple Proof of the Density Hales–Jewett Theorem**](https://doi.org/10.1093/imrn/rnt041), by
Pandelis Dodos, Vassilis Kanellopoulos, and Konstantinos Tyros.
The paper appeared in *International Mathematics Research Notices*, Volume 2014, Issue 12, pages
3340–3352, and the authors' [preprint is available on arXiv](https://arxiv.org/abs/1209.4986).

## Main results

The main theorems are in `DensityHalesJewett/Main.lean`. Their thresholds are stated with
Mathlib's Ackermann function `ack`:

- `Combinatorics.Line.exists_of_density` — the **density Hales–Jewett theorem**. For a finite
  alphabet `α` of `k` letters and a density `δ > 0`, every word length
  `n ≥ ack (4 * k) (k + ⌈1 / δ⌉₊)` has the property that any `A : Finset (Fin n → α)` with
  `δ * k ^ n ≤ #A` contains a combinatorial line, i.e. a Mathlib `Combinatorics.Line α (Fin n)`
  all of whose points lie in `A`.
- `Combinatorics.ArithmeticProgression.exists_of_density_nat` — **Szemerédi's theorem** on the
  integers, obtained from the previous theorem by the digital transfer that reads a number in
  base `k` as a word of length `m` (`Szemeredi.lean`). For `k ≥ 3` and `δ > 0`, every
  `n ≥ ack (4 * k + 1) (k + ⌈1 / δ⌉₊)` has the property that any `A ⊆ range n` with
  `δ * n ≤ #A` contains a nonconstant arithmetic progression of length `k`.
- `Combinatorics.ArithmeticProgression.exists_many_of_density_nat` — **Varnavides' theorem**,
  obtained from the previous theorem by an averaging argument (`Varnavides.lean`). For the same
  `k`, `δ` and `n`, such an `A` contains at least `n ^ 2 / ack (4 * k + 1) (k + ⌈1 / δ⌉₊)`
  arithmetic progressions of length `k`.

The levels `4 * k` and `4 * k + 1` are not optimized.

## Other formalized results

Along the way to the main theorems, the repository develops:

- The finite-unions form of the multidimensional Hales–Jewett theorem, its focusing argument,
  block canonization, and from them the Graham–Rothschild theorem for combinatorial lines
  (`FiniteUnions.lean`, `GrahamRothschild.lean`, `Canonization.lean`).
- The bound by the Ackermann function for the dimensions that the proof produces, which are
  explicit recursions in Shelah's bound `Combinatorics.Line.shelahBound` for the Hales–Jewett
  numbers (`Ackermann.lean`).

It also defines the density Hales–Jewett number `Combinatorics.Line.dhjNumber k δ`, the least `N`
such that the density theorem holds in every dimension `n ≥ N`, and proves the bound
`dhjNumber_le_ack` (`Main.lean`).

## Relation to previous work

The density Hales–Jewett theorem is due to Furstenberg and Katznelson, whose proof is
ergodic-theoretic. The Polymath1 project found the first purely combinatorial proof, which the
Dodos–Kanellopoulos–Tyros paper simplifies; this repository follows the latter paper. Mathlib
has `Combinatorics.Line` and the colouring Hales–Jewett theorem, on which the statements here are
phrased, but no density version. No novelty is claimed for the mathematics.

The Hales–Jewett theorem with Shelah's bound, and the bound `shelahBound k r < ack 5 (2 * k + r)`,
come from the separate project [`ShelahHalesJewett`](https://github.com/gdahia/ShelahHalesJewett).

## Verification

`Challenge.lean` states the density Hales–Jewett theorem and Szemerédi's theorem, as
`Combinatorics.Line.exists_of_density'` and
`Combinatorics.ArithmeticProgression.exists_of_density_nat'`, with the thresholds above. It
imports Mathlib alone and leaves both proofs as `sorry`; the progression in Szemerédi's theorem
is written out as a first term `a` and a common difference `d ≠ 0`. `Solution.lean` proves the
same two declarations from `Main.lean`.

`comparator.json` sets up the comparison of the two modules: it names the two theorems and permits
only the axioms `propext`, `Quot.sound` and `Classical.choice`. A comparator checks that each
declaration in `Solution` has the same statement as in `Challenge` and that its proof uses no other
axioms.

## Build

Build the project:

```bash
lake exe cache get
lake build
```

## Licence

This repository is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

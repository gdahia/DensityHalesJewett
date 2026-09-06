# DensityHalesJewett

This repository contains the Lean 4 formalization of
[**A Simple Proof of the Density Hales–Jewett Theorem**](https://doi.org/10.1093/imrn/rnt041), by
Pandelis Dodos, Vassilis Kanellopoulos, and Konstantinos Tyros.
The paper appeared in *International Mathematics Research Notices*, Volume 2014, Issue 12, pages
3340–3352, and the authors' [preprint is available on arXiv](https://arxiv.org/abs/1209.4986).

## Main results

The two headline theorems are:

- `Combinatorics.Line.exists_of_density` (`DensityHalesJewett/Main.lean`) — the **density
  Hales–Jewett theorem**. For a finite alphabet `α` and a density `δ > 0`, every word length `n`
  past an explicit bound has the property that any `A : Finset (Fin n → α)` with
  `δ * (Fintype.card α) ^ n ≤ #A` contains a combinatorial line, i.e. a
  Mathlib `Combinatorics.Line α (Fin n)` all of whose points lie in `A`.
- `Combinatorics.ArithmeticProgression.exists_of_density_nat` (`DensityHalesJewett/Szemeredi.lean`)
  — **Szemerédi's theorem** on the integers, obtained from the previous theorem by the digital
  transfer that reads a number in base `k` as a word of length `m`. For `k ≥ 3` and `δ > 0`, every
  sufficiently large `n` has the property that any `A ⊆ range n` with `δ * n ≤ #A` contains a
  nonconstant arithmetic progression of length `k`.

## Other formalized results

Along the way to the main theorems, the repository develops:

- The finite-unions form of the multidimensional Hales–Jewett theorem, its focusing argument, and
  block canonization, culminating in the Graham–Rothschild theorem for combinatorial lines
  (`FiniteUnions.lean`, `GrahamRothschild.lean`, `Canonization.lean`).

Moreover, as a bonus, it also proves:

- Varnavides' averaging argument, upgrading the existence of a single arithmetic progression in a
  dense set to a quadratic lower bound on the number of such progressions
  (`Varnavides.lean`).

## Relation to previous work

The density Hales–Jewett theorem is due to Furstenberg and Katznelson, whose proof is
ergodic-theoretic. The Polymath1 project found the first purely combinatorial proof, which the
Dodos–Kanellopoulos–Tyros paper simplifies; this repository follows the latter paper. While
Mathlib does not currently have a density version, it supplies `Combinatorics.Line` and the
colouring Hales–Jewett theorem, on which the statements here are phrased. No novelty is claimed
for the mathematics: the theorem is due to Furstenberg and Katznelson, the first combinatorial
proof to the Polymath1 project, and the proof formalized here to Dodos, Kanellopoulos, and
Tyros.

## Build

Build the project:

```bash
lake exe cache get
lake build
```

## Licence

This repository is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

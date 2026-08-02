# DensityHalesJewett

This repository contains the Lean 4 formalization of
[**A Simple Proof of the Density Hales–Jewett Theorem**](https://doi.org/10.1093/imrn/rnt041), by
Pandelis Dodos, Vassilis Kanellopoulos, and Konstantinos Tyros.
The paper appeared in *International Mathematics Research Notices*, Volume 2014, Issue 12, pages
3340–3352, and the authors' [preprint is available on arXiv](https://arxiv.org/abs/1209.4986).

The main results are the positive-density combinatorial-line theorem
`Combinatorics.Line.exists_of_density` and its consequence for arithmetic progressions of
arbitrary finite length, Szemerédi's theorem on the integers,
`Combinatorics.ArithmeticProgression.exists_of_density_nat`.
Both are also stated in the asymptotic `Filter.atTop` form in
[`Challenge.lean`](DensityHalesJewett/Challenge.lean), proved using only Mathlib's API.

## Other formalized results

Along the way to the main theorems, the repository develops:

- The finite-unions form of the multidimensional Hales--Jewett theorem, its focusing argument, and
  block canonization, culminating in the Graham--Rothschild theorem for combinatorial lines
  (`FiniteUnions.lean`, `GrahamRothschild.lean`, `Canonization.lean`).

Moreover, as a bonus, it also proves:

- Varnavides' averaging argument, upgrading the existence of a single arithmetic progression in a
  dense set to a quadratic lower bound on the number of such progressions
  (`Varnavides.lean`).

## Build

Build the project:

```bash
lake exe cache get
lake build
```

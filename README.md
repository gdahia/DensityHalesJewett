# DensityHalesJewett

This project is a Lean 4 implementation of the proof in
[A Simple Proof of the Density Hales–Jewett Theorem](https://doi.org/10.1093/imrn/rnt041)
by Pandelis Dodos, Vassilis Kanellopoulos, and Konstantinos Tyros. The published paper appeared in
*International Mathematics Research Notices*, Volume 2014, Issue 12, pages 3340–3352. The authors'
[preprint is available on arXiv](https://arxiv.org/abs/1209.4986).

The proof is purely combinatorial and uses the uniform measure on finite word spaces. The
formalization develops the positive-density combinatorial-line theorem and its consequence for
arithmetic progressions of arbitrary finite length.

## Status

The formalization is in progress. The public challenge statements are in
[`DensityHalesJewett/Challenge.lean`](DensityHalesJewett/Challenge.lean). Type-correct declaration
stubs following the blueprint's dependency layers live in the remaining files under
[`DensityHalesJewett`](DensityHalesJewett), and implementation and review provenance is recorded in
[`formalization.yaml`](formalization.yaml).

## Building

Install the Lean toolchain specified by `lean-toolchain`, then run:

```shell
lake exe cache get
lake build
```

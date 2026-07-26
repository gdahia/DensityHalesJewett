# Divergence between the Dodos–Kanellopoulos–Tyros proof and the Lean argument

## Scope and source

This note compares the current working tree with Pandelis Dodos, Vassilis Kanellopoulos, and
Konstantinos Tyros, *A simple proof of the density Hales–Jewett theorem*,
[arXiv:1209.4986v2](https://arxiv.org/abs/1209.4986) (published in *International Mathematics
Research Notices* 2014, no. 12, 3340–3352).

The arXiv TeX source was downloaded from
`https://export.arxiv.org/e-print/1209.4986`. The downloaded gzip stream is 12,063 bytes with
SHA-256
`aaf669f5f28f3df4e4cea8db1946992dcd8fd338652bc87854ae90cc32ca7f84`; it expands to the
single 503-line file `Density_Hales-Jewett_Final.tex`. The local inspection copies are
`/tmp/dodos-dhj-1209.4986.tar` and `/tmp/Density_Hales-Jewett_Final.tex`; they are not vendored
into the repository.

The Lean module `DensityHalesJewett.Main` currently builds, but only with three `sorry` warnings:
two in `GrahamRothschild.lean` and one at the uniform-fibers step in
`UniformFibers.lean`. The latter is the architectural problem discussed here.

## Executive conclusion

The main divergence is not in the later density arithmetic. It occurs at the formalization of
paper Lemma 4.

Paper Lemma 4 finds an `m`-dimensional subspace in a **proper initial segment** of the coordinates
and leaves a nonempty suffix on which all the corresponding fibers remain dense. The current Lean
predicate fixes the entire prefix dimension in advance and asks for a subspace of that whole
prefix. When its suffix parameter is zero, the predicate says that every sufficiently dense set
already contains an `m`-dimensional subspace. Thus it contains multidimensional density
Hales–Jewett for the same alphabet.

That stronger statement is mathematically true after density Hales–Jewett has been proved, but it
cannot be used to prove the induction step from `DHJ(k)` to `DHJ(k+1)`. Doing so is circular. The
current worktree has correctly exposed the issue by leaving
`exists_uniformFibersFinSufficient_block_iteration` as `sorry` and by adding a valid conditional
helper that assumes `HasDensityHJ alphabet`. That conditional helper diagnoses the strength of the
current predicate; it is not a non-circular replacement for paper Lemma 4.

The same mismatch propagates to two places:

1. the correlated-fibers and restricted-alphabet arguments, corresponding to paper Lemma 7 and
   Corollary 5; and
2. the one-insensitive-set tiling argument, corresponding to paper Lemma 12.

The fix is to formalize the variable-cut statement of paper Lemma 4, thread the resulting prefix
and suffix through the correlated-fibers and restricted-alphabet proofs, and rebuild the base
tiling lemma using Corollary 5 and insensitivity, as the paper does.

## Proof map

| Paper | Current Lean | Assessment |
|---|---|---|
| Proposition 3: multidimensional DHJ from `DHJ(k)` | `Subspace.exists_eventually_of_density` | Substantively aligned |
| Lemma 4: variable-cut uniform fibers | `Subspace.UniformFibersFinSufficient` and `uniformFibersBound` | **Not aligned; circularly stronger** |
| Corollary 5: a dense set over `k+1` contains the `k`-restriction of a subspace | `exists_eventually_restrictAlphabet_subset` | Strategy is recognizable, but depends on the stronger uniform-fibers predicate |
| Proposition 2 and Lemma 7: line-color canonization after uniformizing fibers | `exists_uniform_fibers_and_homogeneous_lines` through `exists_subspace_correlated_fibers` | Mostly aligned after the uniform-fibers interface is repaired |
| Lemma 8: density increment or many lines | `exists_subspace_many_lines` | Aligned in its averaging argument; its entry point uses the wrong fixed-prefix bound |
| Lemma 10 and Corollary 11: correlation with an intersection of insensitive sets | endpoint-family and first-failure lemmas in `DensityIncrement.lean` | Substantively aligned, with smaller conservative numerical parameters |
| Lemma 12: tile one insensitive set | `IsInsensitive.exists_tilingSufficient_dimension` | **Not aligned; currently derives a subspace from arbitrary density and does not use insensitivity** |
| Corollary 13: tile an intersection of insensitive sets | intersection-tiling induction in `Insensitive.lean` | Structurally aligned once the one-set base case is fixed |
| Proposition 6: line or density increment | `density_increment` | Structurally aligned, conditional on the earlier repairs |
| “Standard iteration” after Proposition 6 | the explicit schedule in `Main.lean` | Legitimate and useful elaboration of the paper |

## The exact mismatch at Lemma 4

### What the paper proves

For `k ≥ 2`, `m ≥ 1`, `0 < ε < 1`, and sufficiently large `n`, paper Lemma 4 says that every
`A ⊆ [k]^n` of density greater than `ε` admits:

- a cut `l < n`;
- an `m`-dimensional subspace `V ⊆ [k]^l`; and
- for every `x ∈ V`, a suffix fiber
  `A_x = {y ∈ [k]^(n-l) | x⌢y ∈ A}`

such that

`dens(A_x) ≥ dens(A) - ε`.

The strict inequality `l < n` is part of the mathematical content. The proof examines successive
blocks of `m` coordinates. If a block is not uniformly good, averaging selects a prefix with a
fixed positive density increment. The density cannot increase indefinitely, so a good block
appears before all coordinates are consumed. The output is a subspace in that block together with
the still-unfixed remaining coordinates.

The paper uses this shape directly:

- in Corollary 5, it averages over the remaining suffix and only then applies `DHJ(k)` inside the
  restricted parameter cube;
- in Lemma 7, it uses the remaining suffix to define the common-fiber densities of parameter
  lines; and
- in Lemma 8, it chooses one suffix `y₀` only after two density estimates have been intersected.

### What Lean currently asks for

[`UniformFibersFinSufficient`](DensityHalesJewett/UniformFibers.lean#L385) states, in substance:

```lean
∀ q A, ε < dens A →
  ∃ V : Subspace (Fin dimension) (Fin alphabet) (Fin n),
    ∀ x, dens A - ε ≤ dens (fiber A (V x))
```

Here the subspace occupies the full fixed `Fin n` prefix and only `Fin q` remains as a suffix.
Taking `q = 0` makes every suffix fiber a subset of a singleton. Since `dens A - ε > 0`, every
point of the subspace must belong to `A`. This reduction is implemented explicitly by
[`exists_subspace_of_uniformFibersFinSufficient`](DensityHalesJewett/Insensitive.lean#L124).
Consequently, the current predicate at `q = 0` implies the multidimensional density
Hales–Jewett theorem for `Fin alphabet`.

This also explains why the new helper
[`exists_uniformFibersFinSufficient_of_densityHJ`](DensityHalesJewett/UniformFibers.lean#L421)
works: it assumes exactly the missing theorem, thresholds the full prefix words according to
their suffix-fiber densities, and applies multidimensional DHJ to the resulting positive-density
set. It must not be used with `alphabet = k+1` while proving `DHJ(k+1)`.

The previously proposed consecutive-block proof cannot establish the current predicate. A
consecutive-block argument produces a subspace in the current block and leaves all later
coordinates as a suffix; it does not choose one common value of those later coordinates. Trying
to pad the block subspace by a fixed later word silently changes “each fiber is dense” into “one
later word lies in every fiber.” A middle layer of a Boolean cube gives a concrete obstruction to
the proposed elementary fixed-prefix bound: it has positive density and no combinatorial line.

## How the mismatch becomes circular

The current dependency chain is:

```text
unconditional fixed-prefix uniform fibers
├── correlated fibers / many lines
│   └── structured correlation
│       └── density increment
│           └── DHJ(k+1)
├── restricted-alphabet subspace
│   └── intended input to insensitive tiling
└── q = 0 gives a subspace in any dense set
    └── current insensitive tiling base case
        └── structured-set tiling
            └── density increment
                └── DHJ(k+1)
```

There are two concrete manifestations.

### Correlated fibers and Corollary 5

[`correlatedFibersBound`](DensityHalesJewett/DensityIncrement.lean#L202) chooses a fixed prefix
large enough for the current `uniformFibersBound`. Later,
[`exists_subspace_many_lines`](DensityHalesJewett/DensityIncrement.lean#L912) splits the ambient
cube at exactly that fixed prefix. This is unlike paper Lemma 7, where Lemma 4 itself chooses
`l < n`.

Similarly, [`exists_eventually_restrictAlphabet_subset`](DensityHalesJewett/UniformFibers.lean#L991)
uses `uniformFibersBound (k+1) ...` while only assuming `HasDensityHJ k`. Under the current
fixed-prefix meaning, the missing proof of that bound requires `HasDensityHJ (k+1)`, so this is the
induction hypothesis one is trying to prove, not the hypothesis one actually has.

### The tiling base case

The paper’s Lemma 12 is specifically about an `(i,k+1)`-insensitive set. It uses Corollary 5 to
find a subspace whose restriction to the first `k` letters lies in a dense fiber, and then uses
insensitivity to extend containment to the full `k+1`-letter subspace. Its staged block
construction is needed because removing tiles does not leave a globally insensitive set; only
the relevant later block sections retain insensitivity.

The current
[`exists_tilingSufficient_dimension`](DensityHalesJewett/Insensitive.lean#L209) instead:

- obtains the stronger unconditional uniform-fibers statement;
- takes its `q = 0` specialization to find a subspace in any dense uncovered set; and
- applies a maximal-packing argument.

The letter `i` and the hypothesis that `D` is insensitive are intentionally unused in this proof.
That is a decisive sign that the argument is not paper Lemma 12: it is proving the stronger claim
that every dense set can be almost tiled by subspaces, which already requires DHJ for the full
`k+1`-letter alphabet.

A maximal-packing proof cannot be repaired merely by applying Corollary 5 to the uncovered set.
After arbitrary subspace ranges are removed, the uncovered set need not remain insensitive.
Either the paper’s staged block invariant must be formalized, or a different construction must
prove an equivalent sectionwise-insensitivity invariant.

## Required repair

### 1. Replace the uniform-fibers interface with the paper-shaped statement

The public statement should quantify over a total dimension and return a proper coordinate split.
An implementation-oriented shape is:

```lean
def UniformFibersFinSufficient
    (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin alphabet), ε < (A.dens : ℝ) →
    ∃ p q, ∃ e : Fin p ⊕ Fin q ≃ Fin n,
      0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A' (V x)).dens : ℝ)
```

Equivalent formulations using `p < n` and `q = n-p` are fine. The important requirements are:

- the subspace is only in the returned prefix;
- the suffix is returned, not fixed;
- the suffix has positive coordinate length; and
- the theorem is proved by the elementary density-increment block iteration, without any
  `HasDensityHJ` assumption.

The internal induction should expose the paper’s state: the number of consumed `dimension`-blocks,
the currently fixed prefix word, its fiber density, and the remaining coordinate block. The
termination inequality should be proved from the explicit paper bound or from a slightly larger
integer ceiling. No heartbeat increase is needed or appropriate.

The conditional full-prefix helper may be deleted or retained under a name that makes its DHJ
dependence explicit, but it must not feed the alphabet-size induction.

### 2. Rewire Lemma 7 and Corollary 5 around the returned split

For correlated fibers:

1. apply the repaired Lemma 4 to the entire reindexed ambient set;
2. retain its returned prefix subspace and suffix type;
3. perform Graham–Rothschild canonization inside that prefix subspace;
4. prove the good alternative exactly as now; and
5. fix a suffix only at the Lemma 8 averaging step.

Thus `correlatedFibersBound`/`manyLinesBound` should be total ambient-dimension bounds, not sizes of
a prefix that is assumed sufficient for every suffix dimension.

For Corollary 5:

1. apply the repaired Lemma 4 over `Fin (k+1)` with parameter dimension
   `M = MDHJ(k,m,δ/2)`;
2. restrict the returned parameter cube to `Fin k`;
3. average over the returned suffix to obtain a dense `Fin k` parameter family above one suffix;
4. apply `HasDensityHJ k` through multidimensional DHJ; and
5. extend the restricted subspace back to `Fin (k+1)`.

This removes every use of `uniformFibersBound (k+1) ...` whose proof would require
`HasDensityHJ (k+1)`.

### 3. Reimplement the one-insensitive-set tiling lemma

The base tiling theorem must explicitly depend on `HasDensityHJ k`, directly or through the
repaired restricted-alphabet bound. Follow paper Lemma 12:

1. choose the block size `M₁` from Corollary 5;
2. on a positive-density family of contexts, find an `m`-subspace in the next `M₁`-block whose
   `Fin k` restriction lies in the relevant section;
3. use `(i,k+1)`-insensitivity to obtain the entire `Fin (k+1)` subspace;
4. pigeonhole to one repeated local subspace and add the corresponding disjoint tiles;
5. record that every later block section of the residual is still insensitive; and
6. iterate until the uncovered density is below `2β`.

The existing intersection-tiling induction can then remain largely unchanged: it is the Lean
counterpart of paper Corollary 13, expressed with abstract bounds and composed subspaces.

The tiling-bound definitions and specifications will need to accept or encode
`HasDensityHJ k`. This assumption is available in `DensityIncrement.density_increment` and is the
correct lower-alphabet induction hypothesis.

### 4. Rebuild upward through the dependency graph

The recommended order is:

1. `UniformFibers.lean`: variable-cut Lemma 4 and the repaired Corollary 5;
2. `Insensitive.lean`: paper Lemma 12, then the existing intersection induction;
3. `DensityIncrement.lean`: adapt correlated-fiber bounds and split handling;
4. `Main.lean`: rebuild the alphabet induction unchanged except for new bound interfaces.

After each stage, run `lake build` on the affected module and resolve all warnings and linter
messages. The repair is complete only when the uniform-fibers and tiling paths contain no
`HasDensityHJ (k+1)` assumption, explicit or hidden in a selected bound.

## What should be preserved

Several departures from the paper are useful and should not be undone:

- The Lean proof gives the “standard iteration” after Proposition 6 explicitly via a backward
  dimension schedule.
- The endpoint-family formalization of insensitive intersections is a faithful concrete version
  of paper Lemma 10.
- The use of minima in `η` and `γ` makes auxiliary inequalities and monotonicity explicit while
  only shrinking the positive increment.
- Abstract finite packings and composition lemmas in the intersection-tiling layer are reusable;
  only the circular one-set base case must be replaced.

The central correction is therefore localized in concept, though not in line count: restore the
paper’s unfixed suffix at Lemma 4 and preserve that information until the paper itself chooses a
suffix.

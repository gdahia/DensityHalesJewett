# `DensityHalesJewett.Subspace.exists_uniformFibersFinSufficient`

Source: `DensityHalesJewett/UniformFibers.lean`.

## Feasibility audit

The former consecutive-block plan was false. At suffix dimension zero, the conclusion says that
every family of density greater than `ε` contains a complete `dimension`-dimensional
combinatorial subspace. Thus this theorem contains multidimensional density Hales--Jewett for
`Fin alphabet`; numerical block-loss and exhaustion inequalities alone cannot prove it.

For example, with binary alphabet and one parameter, an admissible small numerical fuel can have
a middle Boolean layer of density greater than `ε`. That layer is an antichain and contains no
binary combinatorial line. This rules out the deleted assertion that every admissible
`fuel * dimension` is sufficient.

## Implemented conditional reduction

`exists_uniformFibersFinSufficient_of_densityHJ` is the correct proof once
`HasDensityHJ alphabet` is available:

1. For `A` define
   `good := {x | dens A - ε ≤ dens (fiber A x)}`.
2. `average_density_fiber` says that the average of the fiber-density function is `dens A`.
3. Apply `density_ge_threshold` with threshold `dens A - ε`. Since `ε < dens A ≤ 1`, its lower
   bound
   `ε / (1 - (dens A - ε))`
   is at least `ε`; hence `good` has density at least `ε`.
4. Apply `exists_eventually_of_density hDHJ` to `good` and obtain a
   `dimension`-subspace contained in it. Membership in `good` is exactly the required fiber
   inequality.
5. The empty alphabet is handled separately by taking prefix dimension `dimension`; the positive
   dimension makes the ambient word type empty, contradicting the density hypothesis.

This conditional helper is implemented and Lake-checked.

## Why the unconditional declaration is not currently implementable

The file later uses this theorem at alphabet `k + 1` while the global induction assumes only
`HasDensityHJ k`. Applying the implemented conditional helper would assume the induction target
and make the proof circular. The theorem is mathematically true, but proving it here would itself
prove the density Hales--Jewett result that the rest of the repository is intended to establish.

## Required argument rewrite

The fixed-prefix predicate must not be weakened merely to restricted parameter words. The
many-lines argument later averages fiber densities over the full `Fin (k + 1)` parameter cube, so
it genuinely needs the full-parameter conclusion of paper Lemma 4. What must change is the
coordinate interface: the subspace lies in a proper prefix selected by the proof, while the
remaining coordinates stay as an unfixed suffix.

### 1. Replace the fixed-prefix predicate by variable-cut uniform fibers

Define a sufficiency predicate for a total ambient dimension. Given
`A : Finset (Fin n → Fin alphabet)`, it should return:

- natural numbers `p q`;
- an equivalence `e : Fin p ⊕ Fin q ≃ Fin n`;
- a proof that `0 < q`;
- a subspace
  `V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p)`; and
- after transporting `A` along `e`, the estimate
  `dens A - ε ≤ dens (fiber A' (V x))` for every full parameter word
  `x : Fin dimension → Fin alphabet`.

An equivalent interface using `p < n` and `q = n - p` is acceptable. The essential invariant is
that the suffix is returned and remains unfixed.

Prove eventual sufficiency by the elementary block density-increment argument of Dodos,
Kanellopoulos, and Tyros, Lemma 4. The induction state should record:

1. the number of consumed `dimension`-blocks;
2. the word fixed on those blocks;
3. the density of the resulting fiber; and
4. the unconsumed coordinate block.

If the next block is not uniformly good, averaging supplies a choice that raises the current
fiber density by a fixed positive amount. The density upper bound forces termination while a
nonempty suffix remains. Follow the shared bound policy: an Archimedean fuel witness and
`Nat.find` are sufficient; the paper's closed numerical bound need not be exposed.

The existing conditional helper
`exists_uniformFibersFinSufficient_of_densityHJ` may be retained under a name that explicitly says
it proves the stronger full-fixed-prefix result, or removed if unused. It must not feed the
alphabet-size induction.

### 2. Rewire correlated fibers and the restricted-alphabet lemma

In `DensityIncrement.exists_uniform_fibers_and_homogeneous_lines` and its callers:

1. apply the variable-cut lemma to the entire ambient family;
2. retain the returned prefix subspace and suffix type;
3. perform Graham--Rothschild line canonization inside that prefix subspace;
4. carry the full-parameter fiber estimate into the many-lines argument; and
5. fix a suffix only at the later averaging step corresponding to paper Lemma 8.

Consequently `correlatedFibersBound` and `manyLinesBound` should bound the total ambient
dimension, not a fixed prefix required to work for every suffix dimension.

Reprove `exists_eventually_restrictAlphabet_subset`, corresponding to paper Corollary 5, from the
same variable-cut lemma:

1. uniformize a dense `Fin (k + 1)` family on a returned prefix;
2. restrict that parameter cube to `Fin k`;
3. average over the returned suffix;
4. apply multidimensional density Hales--Jewett using `HasDensityHJ k`; and
5. extend the restricted subspace back to `Fin (k + 1)`.

This route uses the lower-alphabet induction hypothesis only where the paper uses it and never
requires `HasDensityHJ (k + 1)`.

### 3. Reimplement the one-insensitive-set tiling base case

`Insensitive.exists_tilingSufficient_dimension` must no longer apply the suffix-zero specialization
to an arbitrary uncovered family. Its replacement should follow paper Lemma 12 and explicitly
depend on `HasDensityHJ k`, directly or through the repaired restricted-alphabet bound:

1. choose a block size from the restricted-alphabet subspace theorem;
2. find an `m`-subspace whose `Fin k` restriction lies in a dense block section;
3. use `(i, k + 1)`-insensitivity to extend containment to the full
   `Fin (k + 1)` subspace;
4. pigeonhole to a repeated local subspace and add all corresponding disjoint tiles;
5. maintain the invariant that the relevant sections in every later block remain insensitive;
   and
6. repeat until the uncovered density is below `2 * β`.

The existing unrestricted maximal-packing argument is not a replacement for this invariant:
removing arbitrary subspace ranges need not leave a globally insensitive uncovered family.

After the one-set base case is repaired, retain the current intersection-tiling induction, which
is the counterpart of paper Corollary 13. Change the tiling-bound definitions and specification
theorems to accept or encode `HasDensityHJ k`, following the shared bound policy.

### 4. Remove the circular dependency and rebuild upward

Remove `uniformFibersBound` with its current unconditional fixed-prefix meaning. A variable-cut
bound remains unconditional because paper Lemma 4 is elementary. Bounds for restricted-alphabet
subspaces and insensitive tilings must be selected under `if h : HasDensityHJ k` and expose
specification theorems taking `h` explicitly.

Rebuild in dependency order:

1. `DensityHalesJewett.UniformFibers`;
2. `DensityHalesJewett.Insensitive`;
3. `DensityHalesJewett.DensityIncrement`; and
4. `DensityHalesJewett.Main`.

This is an architectural correction, not a missing local calculation. Reintroducing an
unconditional elementary proof of the old fixed-prefix predicate would recreate the circularity.

## Verification

Build `DensityHalesJewett.UniformFibers`, `DensityHalesJewett.Insensitive`,
`DensityHalesJewett.DensityIncrement`, and `DensityHalesJewett.Main` after changing the dependency
direction. No theorem used to prove `HasDensityHJ (k + 1)` may assume it.

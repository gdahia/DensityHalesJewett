/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.GrahamRothschild

/-!
# Preliminary density lemmas

Multidimensional density Hales--Jewett, uniform fibers, and the restricted-alphabet subspace
lemma.  All subspaces below are mathlib's `Combinatorics.Subspace`.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- The density Hales--Jewett assertion for the alphabet `Fin k`. -/
def HasDensityHJ (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ #A → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A

namespace Subspace

/-- A bound for multidimensional density Hales--Jewett. -/
opaque densityBound (k m : ℕ) (δ : ℝ) : ℕ

/-- Multidimensional density Hales--Jewett follows from the one-dimensional assertion. -/
theorem exists_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  sorry

/-- A sufficient prefix size for finding a subspace above all of whose points the fibers remain
dense. -/
opaque uniformFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ

/-- Uniform fibers on a subspace. -/
theorem exists_fibers_dense {α ι κ : Type*} [Fintype α] [Fintype ι]
    [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hι : uniformFibersBound (Fintype.card α) m ε ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → α)) (hA : ε < (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) α ι,
      ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A (V x)).dens : ℝ) := by
  sorry

/-- A bound for the restricted-alphabet subspace lemma. -/
opaque restrictAlphabetBound (k m : ℕ) (δ : ℝ) : ℕ

/-- A dense family over `Fin (k+1)` contains the `Fin k` restriction of a subspace. -/
theorem exists_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1)))
    (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  sorry

end Subspace
end DensityHalesJewett

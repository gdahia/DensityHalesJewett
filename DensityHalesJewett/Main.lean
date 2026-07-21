/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.DensityIncrement
public import Mathlib.Combinatorics.SetFamily.LYM

/-!
# Density Hales--Jewett

The binary base case and induction on the alphabet size.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Identify a binary word with the coordinates on which it equals `1`. -/
def binarySupport {ι : Type*} [Fintype ι] (w : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i ↦ w i = 1

/-- Two binary words are the ordered points of a combinatorial line exactly when their supports
are strictly comparable. -/
theorem binary_line_iff_ssubset {ι : Type*} [Fintype ι] (x y : ι → Fin 2) :
    (∃ l : Combinatorics.Line (Fin 2) ι, l 0 = x ∧ l 1 = y) ↔
      binarySupport x ⊂ binarySupport y := by
  sorry

/-- Density Hales--Jewett for the binary alphabet. -/
theorem dhj_two : HasDensityHJ 2 := by
  sorry

/-- Density Hales--Jewett for every finite alphabet of cardinality at least two. -/
theorem density_hales_jewett_fin (k : ℕ) (hk : 2 ≤ k) : HasDensityHJ k := by
  sorry

end DensityHalesJewett

namespace Combinatorics.Line

/-- A threshold for the density Hales--Jewett theorem over an alphabet of size `k`. -/
opaque densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ

theorem exists_of_density (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  sorry

end Combinatorics.Line

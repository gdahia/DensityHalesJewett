/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-5.6 Sol, Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.Corner.Roth
public import Mathlib.Combinatorics.HalesJewett

/-!
# Density theorem challenge statements

This file records density-theorem interfaces for arithmetic progressions and
combinatorial lines.
-/

@[expose] public section

open Finset

namespace Combinatorics

/-- A nonconstant arithmetic progression of length `k` in an additive monoid. -/
@[ext]
structure ArithmeticProgression (α : Type*) [AddMonoid α] (k : ℕ) where
  /-- The initial term of the arithmetic progression. -/
  start : α
  /-- The common difference of the arithmetic progression. -/
  diff : α
  diff_ne_zero : diff ≠ 0

namespace ArithmeticProgression

/-- The term of `P` indexed by `i`. -/
def term {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (i : Fin k) : α :=
  P.start + (i : ℕ) • P.diff

/-- The proposition that every term of `P` belongs to `s`. -/
def IsSubset {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (s : Set α) : Prop :=
  ∀ i, P.term i ∈ s

end ArithmeticProgression
end Combinatorics

namespace Combinatorics.ArithmeticProgression

/-- A threshold for the density theorem for arithmetic progressions of length `k`. -/
opaque densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ

theorem exists_of_density_nat (k : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hAδ : δ * n ≤ #A) :
    ∃ P : ArithmeticProgression ℕ k, P.IsSubset (A : Set ℕ) := by
  sorry

end Combinatorics.ArithmeticProgression

namespace Combinatorics.Line

/-- A threshold for the density Hales--Jewett theorem over an alphabet of size `k`. -/
opaque densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ

theorem exists_of_density (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  sorry

end Combinatorics.Line

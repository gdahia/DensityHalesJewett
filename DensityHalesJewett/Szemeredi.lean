/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Main
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Arithmetic progressions from combinatorial lines

Fixed-length base encoding and the digital transfer from density Hales--Jewett to Szemeredi's
theorem on finite intervals.
-/

@[expose] public section

open Finset
open Combinatorics

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

namespace DensityHalesJewett

/-- Encode a fixed-length word as a natural number in base `k`. -/
def baseEncode (k m : ℕ) (x : Fin m → Fin k) : ℕ :=
  ∑ i, (x i : ℕ) * k ^ (i : ℕ)

/-- Fixed-length base-`k` encoding is a bijection with the initial interval of length `k^m`. -/
noncomputable def baseEncodeEquiv (k m : ℕ) (hk : 1 ≤ k) :
    (Fin m → Fin k) ≃ Fin (k ^ m) := by
  sorry

namespace Line

/-- A base-encoded combinatorial line is a nonconstant arithmetic progression. -/
theorem baseEncode_isArithmeticProgression {k m : ℕ} (hk : 1 ≤ k)
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ∃ P : Combinatorics.ArithmeticProgression ℕ k,
      ∀ a, P.term a = baseEncode k m (l a) := by
  sorry

end Line

/-- A sufficiently dense initial interval has a complete digit block with at least half the
ambient density. -/
theorem exists_dense_digitBlock {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 2 * K / δ ≤ N) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : δ * N ≤ #A) :
    ∃ q : ℕ, (q + 1) * K ≤ N ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
  sorry

end DensityHalesJewett

namespace Combinatorics.ArithmeticProgression

/-- A threshold for the density theorem for arithmetic progressions of length `k`. -/
opaque densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ

theorem exists_of_density_nat (k : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hAδ : δ * n ≤ #A) :
    ∃ P : ArithmeticProgression ℕ k, P.IsSubset (A : Set ℕ) := by
  sorry

end Combinatorics.ArithmeticProgression

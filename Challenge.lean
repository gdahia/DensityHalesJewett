/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Computability.Ackermann
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The density theorems with the Ackermann function as the bound

The density Hales--Jewett theorem and Szemerédi's theorem, each for every `n` above a value of
Mathlib's Ackermann function `ack`. This module imports Mathlib alone; the proofs are in the
companion `Solution` module.

A *combinatorial line* in the cube of words of length `n` over a finite alphabet `α` is a family
of `#α` words, one for each letter `x : α`, obtained from a single pattern by filling every
occurrence of a wildcard with `x`; at least one coordinate must be a wildcard, so the line is
nonconstant. This is Mathlib's `Combinatorics.Line α (Fin n)`, and `l x` is the word of the line
indexed by the letter `x`.
-/

@[expose] public section

open Finset

namespace Combinatorics.Line

/-- The **density Hales--Jewett theorem**: over a finite alphabet `α` of `k` letters, in every
dimension `n ≥ ack (4 * k) (k + ⌈1 / δ⌉₊)`, every set of at least a `δ` fraction of the words of
length `n` contains a combinatorial line. -/
theorem exists_of_density' {α : Type*} [Fintype α] {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : ack (4 * Fintype.card α) (Fintype.card α + ⌈1 / δ⌉₊) ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A :=
  sorry

end Combinatorics.Line

namespace Combinatorics.ArithmeticProgression

/-- **Szemerédi's theorem**: for `k ≥ 3` and `n ≥ ack (4 * k + 1) (k + ⌈1 / δ⌉₊)`, every subset of
`range n` with at least `δ * n` elements contains an arithmetic progression of length `k`, i.e.
`k` terms `a, a + d, a + 2 * d, …` with `d ≠ 0`. -/
theorem exists_of_density_nat' {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : ack (4 * k + 1) (k + ⌈1 / δ⌉₊) ≤ n) (A : Finset ℕ) (hAn : A ⊆ range n)
    (hAδ : δ * n ≤ #A) : ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A :=
  sorry

end Combinatorics.ArithmeticProgression

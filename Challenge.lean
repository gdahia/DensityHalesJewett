/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Asymptotic forms of the density theorems

The density Hales--Jewett theorem and Szemeredi's theorem, stated for all sufficiently large `n`
via the `Filter.atTop` filter instead of an explicit threshold. This module imports Mathlib alone;
the proofs are supplied by the companion `Solution` module.

A *combinatorial line* in the cube of words of length `n` over a finite alphabet `α` is a family
of `#α` words, one for each letter `x : α`, obtained from a single pattern by filling every
occurrence of a wildcard with `x`; at least one coordinate must be a wildcard, so the line is
nonconstant. This is Mathlib's `Combinatorics.Line α (Fin n)`, and `l x` is the word of the line
indexed by the letter `x`.
-/

@[expose] public section

open Filter Finset

namespace Combinatorics.Line

/-- The **Density Hales--Jewett theorem**: for a positive density `δ`, every sufficiently long word
length `n` has the property that any set of at least a `δ` fraction of the words of length `n`
over `α` contains a combinatorial line. -/
theorem exists_of_density_atTop (α : Type*) [Fintype α] [Nontrivial α] (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset (Fin n → α), δ * (Fintype.card α : ℝ) ^ n ≤ #A →
      ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A :=
  sorry

end Combinatorics.Line

namespace Combinatorics.ArithmeticProgression

/-- **Szemeredi's theorem**: for a positive density `δ`, every sufficiently large `n` has the
property that any subset of `range n` of size at least `δ * n` contains an arithmetic progression
of length `k`, i.e. `k` terms `a, a + d, a + 2 * d, …` with `d ≠ 0`. -/
theorem exists_of_density_nat_atTop (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset ℕ, A ⊆ range n → δ * n ≤ #A →
      ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A :=
  sorry

end Combinatorics.ArithmeticProgression

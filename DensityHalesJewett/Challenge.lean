/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Szemeredi

/-!
# Asymptotic forms of the density theorems

The density Hales--Jewett theorem and Szemeredi's theorem, stated for all sufficiently large `n`
via the `Filter.atTop` filter instead of an explicit threshold.
-/

@[expose] public section

open Filter Finset
open Combinatorics

namespace Combinatorics.Line

/-- **Density Hales--Jewett theorem**: for a positive density `δ`, every sufficiently long word
length `n` has the property that any set of at least a `δ` fraction of the words of length `n`
over `α` contains a combinatorial line. -/
theorem exists_of_density_atTop (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset (Fin n → α), δ * (Fintype.card α : ℝ) ^ n ≤ #A →
      ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  refine eventually_atTop.2 ⟨densityTheoremBound (Fintype.card α) δ, ?_⟩
  intro n hn A hAδ
  exact exists_of_density α δ hδ n hn A hAδ

end Combinatorics.Line

namespace Combinatorics.ArithmeticProgression

/-- **Szemeredi's theorem**: for a positive density `δ`, every sufficiently large `n` has the
property that any subset of `range n` of size at least `δ * n` contains an arithmetic progression
of length `k`. -/
theorem exists_of_density_nat_atTop (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset ℕ, A ⊆ range n → δ * n ≤ #A →
      ∃ P : ArithmeticProgression ℕ k, P.IsSubset (A : Set ℕ) := by
  refine eventually_atTop.2 ⟨densityTheoremBound k δ, ?_⟩
  intro n hn A hAn hAδ
  exact exists_of_density_nat k hk δ hδ n hn A hAn hAδ

end Combinatorics.ArithmeticProgression

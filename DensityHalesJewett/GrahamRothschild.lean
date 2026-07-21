/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Subspace

/-!
# The Graham--Rothschild theorem for combinatorial lines

The finite-unions focusing argument, block canonization, and the line-coloring form of the
Graham--Rothschild theorem needed by the density proof.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

namespace FiniteUnions

/-- A Hales--Jewett dimension sufficient to focus `q` color profiles simultaneously. -/
opaque focusBound (alphabet colors q : ℕ) : ℕ

/-- The simultaneous color-profile focusing step used in the finite-unions argument. -/
theorem focus (A C U : Type*) [Fintype A] [Fintype C] [Fintype U]
    (n : ℕ) (hn : focusBound (Fintype.card A) (Fintype.card C) (Fintype.card U) ≤ n)
    (χ : U → (Fin n → A) → C) :
    ∃ l : Combinatorics.Line A (Fin n), ∀ u, ∃ c, ∀ a, χ u (l a) = c := by
  sorry

/-- A dimension sufficient for the finite-unions theorem. -/
opaque bound (colors m : ℕ) : ℕ

/-- The finite-unions theorem in ordered block-sequence form. -/
theorem exists_mono (C : Type*) [Finite C] (m : ℕ) :
    ∃ L, ∀ χ : Finset (Fin L) → C,
      ∃ B : Fin m → Finset (Fin L),
        (∀ i, (B i).Nonempty) ∧
        (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
        ∃ c, ∀ I : Finset (Fin m), I.Nonempty → χ (I.biUnion B) = c := by
  sorry

end FiniteUnions

namespace GrahamRothschild

/-- The variable coordinates of a combinatorial line. -/
def variableSet {α ι : Type*} [Fintype ι] (l : Combinatorics.Line α ι) : Finset ι :=
  Finset.univ.filter fun i ↦ l.idxFun i = none

/-- A block-canonization dimension. -/
opaque canonizationBound (alphabet colors blocks : ℕ) : ℕ

/-- Block canonization: inside a suitable subspace, the color of a line depends only on its
variable directions and not on its fixed letters. -/
theorem canonize (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (L n : ℕ)
    (hn : canonizationBound (Fintype.card α) (Fintype.card C) L ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin L) α (Fin n),
      ∀ p q : Combinatorics.Line α (Fin L), variableSet p = variableSet q →
        χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q) := by
  sorry

/-- A Graham--Rothschild dimension for colorings of combinatorial lines. -/
opaque bound (alphabet colors dimension : ℕ) : ℕ

/-- The line case of the Graham--Rothschild theorem. -/
theorem lines (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  sorry

/-- The two-color form of Graham--Rothschild used by the density argument. -/
theorem lines_twoColor (α : Type*) [Fintype α] [Nontrivial α] [DecidableEq α]
    (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) 2 m ≤ n)
    (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∉ L) := by
  sorry

end GrahamRothschild
end DensityHalesJewett

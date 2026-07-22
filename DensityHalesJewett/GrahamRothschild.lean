/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Subspace
import Mathlib.Logic.Equiv.Fin.Basic

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
lemma exists_focus_dimension (alphabet colors q : ℕ) (halphabet : 0 < alphabet) :
    ∃ N, ∀ n ≥ N, ∀ χ : (Fin n → Fin alphabet) → Fin q → Fin colors,
      ∃ l : Combinatorics.Line (Fin alphabet) (Fin n), ∃ c, ∀ a, χ (l a) = c := by
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension
    (Fin alphabet) (Fin q → Fin colors)
  let e := Fintype.equivFin ι
  let N := Fintype.card ι
  refine ⟨N, ?_⟩
  intro n hn
  rw [← Nat.add_sub_of_le hn]
  intro χ
  let x₀ : Fin alphabet := ⟨0, halphabet⟩
  obtain ⟨l, c, hc⟩ := hι fun w i ↦
    χ (Fin.addCases (fun j ↦ w (e.symm j)) (fun _ ↦ x₀)) i
  let l' : Combinatorics.Line (Fin alphabet) (Fin (N + (n - N))) :=
    { idxFun := Fin.addCases (fun i ↦ l.idxFun (e.symm i)) (fun _ ↦ some x₀)
      proper := by
        obtain ⟨i, hi⟩ := l.proper
        refine ⟨Fin.castAdd (n - N) (e i), ?_⟩
        simp only [Fin.addCases_left, e, Equiv.symm_apply_apply, hi] }
  refine ⟨l', c, ?_⟩
  intro a
  funext i
  convert congrFun (hc a) i using 1
  apply congrArg (fun w ↦ χ w i)
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [l', Combinatorics.Line.coe_apply, Fin.addCases_left]
  · intro i
    simp only [l', Combinatorics.Line.coe_apply, Fin.addCases_right, Option.getD_some]

/-- A Hales--Jewett dimension sufficient to focus `q` color profiles simultaneously. -/
noncomputable def focusBound (alphabet colors q : ℕ) : ℕ :=
  by
    classical
    exact if halphabet : 0 < alphabet then
      Nat.find (exists_focus_dimension alphabet colors q halphabet)
    else 0

lemma focusBound_spec (alphabet colors q n : ℕ) (halphabet : 0 < alphabet)
    (hn : focusBound alphabet colors q ≤ n) :
    ∀ χ : (Fin n → Fin alphabet) → Fin q → Fin colors,
      ∃ l : Combinatorics.Line (Fin alphabet) (Fin n), ∃ c, ∀ a, χ (l a) = c := by
  classical
  rw [focusBound, dif_pos halphabet] at hn
  exact (Nat.find_spec (exists_focus_dimension alphabet colors q halphabet)) n hn

/-- The simultaneous color-profile focusing step used in the finite-unions argument. -/
lemma focus (A C U : Type*) [Fintype A] [Nonempty A] [Fintype C] [Fintype U]
    (n : ℕ) (hn : focusBound (Fintype.card A) (Fintype.card C) (Fintype.card U) ≤ n)
    (χ : U → (Fin n → A) → C) :
    ∃ l : Combinatorics.Line A (Fin n), ∀ u, ∃ c, ∀ a, χ u (l a) = c := by
  let eA := Fintype.equivFin A
  let eC := Fintype.equivFin C
  let eU := Fintype.equivFin U
  obtain ⟨l, c, hc⟩ := focusBound_spec (Fintype.card A) (Fintype.card C) (Fintype.card U) n
    (Fintype.card_pos_iff.mpr inferInstance) hn fun w u ↦
      eC (χ (eU.symm u) (eA.symm ∘ w))
  refine ⟨l.map eA.symm, ?_⟩
  intro u
  refine ⟨eC.symm (c (eU u)), ?_⟩
  intro a
  apply eC.injective
  rw [← eA.symm_apply_apply a, Combinatorics.Line.map_apply]
  simpa only [eA, eC, eU, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    Function.comp_apply] using congrFun (hc (eA a)) (eU u)

/-- A dimension sufficient for the finite-unions theorem. -/
opaque bound (colors m : ℕ) : ℕ

/-- The finite-unions theorem in ordered block-sequence form. -/
lemma exists_mono (C : Type*) [Finite C] (m : ℕ) :
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
lemma canonize (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
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
lemma lines (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  sorry

/-- The two-color form of Graham--Rothschild used by the density argument. -/
lemma lines_twoColor (α : Type*) [Fintype α] [Nontrivial α] [DecidableEq α]
    (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) 2 m ≤ n)
    (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∉ L) := by
  classical
  obtain ⟨V, c, hc⟩ :=
    lines α (Fin 2) m n hm hn fun l ↦ if l ∈ L then 0 else 1
  obtain rfl | ⟨c, rfl⟩ := c.eq_zero_or_eq_succ
  · refine ⟨V, Or.inl ?_⟩
    intro l
    by_contra h
    simpa [h] using hc l
  · refine ⟨V, Or.inr ?_⟩
    rw [Fin.eq_zero c] at hc
    intro l h
    simpa [h] using hc l

end GrahamRothschild
end DensityHalesJewett

/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.UniformFibers

/-!
# Insensitive word families and tilings

Boolean closure of insensitive families and the subspace-tiling results used in the density
increment argument.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Two words are equivalent after freely interchanging the letters `i` and `j`. -/
def InsensitiveEquiv {α ι : Type*} (i j : α) (x y : ι → α) : Prop :=
  ∀ a, a ≠ i → a ≠ j → ∀ c, (x c = a ↔ y c = a)

/-- Membership in an `(i,j)`-insensitive family is constant on insensitive-equivalence classes. -/
def IsInsensitive {α ι : Type*} (i j : α) (D : Finset (ι → α)) : Prop :=
  ∀ ⦃x y⦄, InsensitiveEquiv i j x y → (x ∈ D ↔ y ∈ D)

namespace IsInsensitive

/-- Complements preserve insensitivity. -/
lemma compl {α ι : Type*} [Fintype (ι → α)] [DecidableEq (ι → α)]
    {i j : α} {D : Finset (ι → α)} (hD : IsInsensitive i j D) :
    IsInsensitive i j Dᶜ := by
  intro x y hxy
  simp only [mem_compl]
  exact not_congr (hD hxy)

/-- Unions preserve insensitivity. -/
lemma union {α ι : Type*} [DecidableEq (ι → α)]
    {i j : α} {D E : Finset (ι → α)} (hD : IsInsensitive i j D)
    (hE : IsInsensitive i j E) : IsInsensitive i j (D ∪ E) := by
  intro x y hxy
  simp only [mem_union]
  rw [hD hxy, hE hxy]

/-- Intersections preserve insensitivity. -/
lemma inter {α ι : Type*} [DecidableEq (ι → α)]
    {i j : α} {D E : Finset (ι → α)} (hD : IsInsensitive i j D)
    (hE : IsInsensitive i j E) : IsInsensitive i j (D ∩ E) := by
  intro x y hxy
  simp only [mem_inter]
  rw [hD hxy, hE hxy]

/-- The part of `D` left uncovered by a set of subspaces. -/
noncomputable def uncovered {η α ι : Type*} [Fintype (η → α)]
    [DecidableEq (ι → α)] (D : Finset (ι → α))
    (𝒱 : Set (Combinatorics.Subspace η α ι)) : Finset (ι → α) := by
  classical
  exact D.filter fun w ↦ ∀ V ∈ 𝒱, w ∉ Subspace.range V

/-- The intersection of a finite indexed family of finite sets. -/
noncomputable def intersection {r : ℕ} {X : Type*} [Fintype X]
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact Finset.univ.inf D

/-- A sufficient ambient dimension for tiling one insensitive family. -/
opaque tilingBound (k m : ℕ) (β : ℝ) : ℕ

/-- A dense insensitive family can be tiled, up to small error, by disjoint subspaces. -/
lemma exists_disjoint_subspaces {k : ℕ} (i : Fin k)
    (m n : ℕ) (hm : 1 ≤ m) (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : tilingBound k m β ≤ n) (D : Finset (Fin n → Fin (k + 1)))
    (hD : IsInsensitive i.castSucc (Fin.last k) D)
    (hDβ : 2 * β ≤ (D.dens : ℝ)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V D) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered D 𝒱).dens : ℝ) < 2 * β := by
  sorry

/-- A sufficient ambient dimension for tiling an intersection of insensitive families. -/
opaque intersectionTilingBound (k r m : ℕ) (β : ℝ) : ℕ

/-- An intersection of insensitive families can be tiled by disjoint subspaces. -/
lemma exists_disjoint_subspaces_iInter {k : ℕ} (r m n : ℕ)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : intersectionTilingBound k r m β ≤ n)
    (D : Fin r → Finset (Fin n → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (D i))
    (hDβ : 2 * r * β ≤ ((intersection D).dens : ℝ)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V (intersection D)) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered (intersection D) 𝒱).dens : ℝ) < 2 * r * β := by
  sorry

end IsInsensitive
end DensityHalesJewett

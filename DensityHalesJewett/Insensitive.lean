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

@[simp]
lemma mem_intersection {r : ℕ} {X : Type*} [Fintype X]
    {D : Fin r → Finset X} {x : X} :
    x ∈ intersection D ↔ ∀ i, x ∈ D i := by
  classical
  rw [intersection, ← Finset.singleton_subset_iff, Finset.le_inf_iff]
  simp only [Finset.mem_univ, forall_const, Finset.singleton_subset_iff]

/-- An ambient dimension is sufficient for tiling every dense one-pair insensitive family. -/
def TilingSufficient (k m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ i : Fin k, ∀ D : Finset (Fin n → Fin (k + 1)),
    IsInsensitive i.castSucc (Fin.last k) D →
    2 * β ≤ (D.dens : ℝ) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V D) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered D 𝒱).dens : ℝ) < 2 * β

/-- Finite-stage block packing gives one exact sufficient dimension for one-family tiling. -/
lemma exists_tilingSufficient_dimension (k m : ℕ) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, TilingSufficient k m β N := by
  sorry

/-- One-family tiling sufficiency is upward closed after padding with unused final coordinates. -/
lemma exists_eventually_tilingSufficient (k m : ℕ) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, ∀ n ≥ N, TilingSufficient k m β n := by
  sorry

/-- A sufficient ambient dimension for tiling one insensitive family. -/
noncomputable def tilingBound (k m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < β ∧ β ≤ 1 then
    Nat.find (exists_eventually_tilingSufficient k m h.1 h.2.1 h.2.2)
  else 0

/-- The selected one-family tiling bound satisfies the tiling predicate in every larger
dimension. -/
lemma tilingBound_spec (k m n : ℕ) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : tilingBound k m β ≤ n) : TilingSufficient k m β n := by
  classical
  rw [tilingBound, dif_pos ⟨hm, hβ₀, hβ₁⟩] at hn
  exact Nat.find_spec (exists_eventually_tilingSufficient k m hm hβ₀ hβ₁) n hn

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
  exact tilingBound_spec k m n hm hβ₀ hβ₁ hn i D hD hDβ

/-- The preimage of a word family in a subspace parameter cube. -/
noncomputable def parameterPreimage {η α ι : Type*} [Fintype (η → α)]
    [DecidableEq (ι → α)] (V : Combinatorics.Subspace η α ι)
    (D : Finset (ι → α)) : Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ V x ∈ D

/-- Pulling an insensitive family back through a subspace preserves its sensitivity pair. -/
lemma parameterPreimage_isInsensitive {α η ι : Type*}
    [Fintype (η → α)] [DecidableEq (ι → α)]
    {a b : α} (V : Combinatorics.Subspace η α ι) (D : Finset (ι → α))
    (hD : IsInsensitive a b D) :
    IsInsensitive a b (parameterPreimage V D) := by
  classical
  intro x y hxy
  simp only [parameterPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  apply hD
  intro c hca hcb i
  cases hi : V.idxFun i with
  | inl d =>
      rw [V.apply_inl hi, V.apply_inl hi]
  | inr e =>
      rw [V.apply_inr hi, V.apply_inr hi]
      exact hxy c hca hcb e

/-- Composing a finite disjoint family of inner tiles with one outer tile preserves finiteness,
containment, and pairwise-disjointness. -/
lemma composed_inner_tiles_facts {k d M n : ℕ}
    (D : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n))
    (𝒲 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M)))
    (h𝒲 : 𝒲.Finite)
    (hcontained : ∀ W ∈ 𝒲, Subspace.IsContained W (parameterPreimage V D))
    (hpairwise : 𝒲.PairwiseDisjoint fun W ↦
      (Subspace.range W : Set (Fin M → Fin (k + 1)))) :
    let 𝒰 := Subspace.compose V '' 𝒲
    𝒰.Finite ∧
      (∀ U ∈ 𝒰, Subspace.IsContained U D) ∧
      (𝒰.PairwiseDisjoint fun U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
  classical
  refine ⟨h𝒲.image (Subspace.compose V), ?_, ?_⟩
  · intro U hU x
    obtain ⟨W, hW, rfl⟩ := hU
    simp only [Subspace.compose_apply]
    simpa only [parameterPreimage, Finset.mem_filter, Finset.mem_univ, true_and] using
      hcontained W hW x
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    obtain ⟨W, hW, rfl⟩ := hU
    obtain ⟨W', hW', rfl⟩ := hU'
    apply congrArg (Subspace.compose V)
    apply Set.pairwiseDisjoint_iff.mp hpairwise hW hW'
    obtain ⟨z, hz, hz'⟩ := hcommon
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hz
    obtain ⟨y, hy⟩ := Subspace.mem_range.mp hz'
    refine ⟨W x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨y, ?_⟩⟩
    apply Subspace.injective V
    simpa only [Subspace.compose_apply] using hy.trans hx.symm

/-- An ambient dimension is sufficient for tiling every dense intersection of `r` insensitive
families. -/
def IntersectionTilingSufficient (k r m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 1 ≤ r), ∀ hrk : r ≤ k,
    ∀ D : Fin r → Finset (Fin n → Fin (k + 1)),
    (∀ i, IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (D i)) →
    2 * r * β ≤ ((intersection D).dens : ℝ) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V (intersection D)) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered (intersection D) 𝒱).dens : ℝ) < 2 * r * β

/-- Induction on the number of insensitive families gives one exact sufficient intersection-tiling
dimension. -/
lemma exists_intersectionTilingSufficient_dimension (k r m : ℕ)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, IntersectionTilingSufficient k r m β N := by
  sorry

/-- Intersection-tiling sufficiency is upward closed after padding with unused final
coordinates. -/
lemma exists_eventually_intersectionTilingSufficient (k r m : ℕ)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, ∀ n ≥ N, IntersectionTilingSufficient k r m β n := by
  sorry

/-- A sufficient ambient dimension for tiling an intersection of insensitive families. -/
noncomputable def intersectionTilingBound (k r m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ r ∧ r ≤ k ∧ 1 ≤ m ∧ 0 < β ∧ β ≤ 1 then
    Nat.find (exists_eventually_intersectionTilingSufficient
      k r m h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 0

/-- The selected intersection-tiling bound satisfies the tiling predicate in every larger
dimension. -/
lemma intersectionTilingBound_spec (k r m n : ℕ)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : intersectionTilingBound k r m β ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  classical
  rw [intersectionTilingBound,
    dif_pos ⟨hr₀, hrk, hm, hβ₀, hβ₁⟩] at hn
  exact Nat.find_spec
    (exists_eventually_intersectionTilingSufficient k r m hr₀ hrk hm hβ₀ hβ₁) n hn

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
  exact intersectionTilingBound_spec k r m n hr₀ hrk hm hβ₀ hβ₁ hn
    hr₀ hrk D hD hDβ

end IsInsensitive
end DensityHalesJewett

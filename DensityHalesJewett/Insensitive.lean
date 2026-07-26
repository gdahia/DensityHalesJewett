/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.UniformFibers
import Mathlib.Tactic.Linarith
import Mathlib.Order.Preorder.Finite

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

/-- Fix an initial coordinate block and place a subspace on the remaining coordinates. -/
private def padExtraSubspace {α η : Type*} {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin N)) :
    Combinatorics.Subspace η α (Fin n) where
  idxFun i :=
    match e.symm i with
    | Sum.inl j => Sum.inl (z j)
    | Sum.inr j => V.idxFun j
  proper a := by
    obtain ⟨i, hi⟩ := V.proper a
    refine ⟨e (Sum.inr i), ?_⟩
    simp only [Equiv.symm_apply_apply, hi]

@[simp]
private lemma padExtraSubspace_apply {α η : Type*} {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin N)) (x : η → α) :
    padExtraSubspace e z V x =
      DensityHalesJewett.concat z (V x) ∘ e.symm := by
  funext i
  cases hi : e.symm i with
  | inl j =>
      simp [padExtraSubspace, Combinatorics.Subspace.coe_apply, hi,
        DensityHalesJewett.concat, Function.comp_apply]
  | inr j =>
      simp [padExtraSubspace, Combinatorics.Subspace.coe_apply, hi,
        DensityHalesJewett.concat, Function.comp_apply]

/-- Uniform-fiber sufficiency at suffix dimension zero contains a subspace in the family. -/
private lemma exists_subspace_of_uniformFibersFinSufficient
    {alphabet dimension n : ℕ} {ε : ℝ} (_hε : 0 < ε)
    (hfin : Subspace.UniformFibersFinSufficient alphabet dimension ε n)
    (A : Finset (Fin n → Fin alphabet)) (hA : ε < (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n),
      Subspace.IsContained V A := by
  let eCoord := (Equiv.sumEmpty (Fin n) (Fin 0)).symm
  let eWord := eCoord.arrowCongr (Equiv.refl (Fin alphabet))
  let A' := A.map eWord.toEmbedding
  have hA' : (A'.dens : ℝ) = (A.dens : ℝ) := by
    simp only [A', Finset.dens_map_equiv]
  obtain ⟨V, hV⟩ := hfin 0 A' (by rw [hA']; exact hA)
  refine ⟨V, ?_⟩
  intro x
  have hpos : 0 < ((fiber A' (V x)).dens : ℝ) :=
    (sub_pos.mpr (by rw [hA']; exact hA)).trans_le (hV x)
  have hpos' : 0 < (fiber A' (V x)).dens := by
    exact_mod_cast hpos
  obtain ⟨y, hy⟩ := Finset.dens_pos.mp hpos'
  rw [mem_fiber] at hy
  have hword : eWord (V x) = DensityHalesJewett.concat (V x) y := by
    funext i
    rcases i with i | i
    · simp [eWord, eCoord, Equiv.arrowCongr, DensityHalesJewett.concat]
    · exact Fin.elim0 i
  rw [← hword] at hy
  simpa only [A', Finset.mem_map_equiv, Equiv.symm_apply_apply] using hy

/-- A finite word cube admits a maximal finite disjoint packing by contained subspaces. -/
private lemma exists_maximal_subspace_packing
    {alphabet dimension n : ℕ} (halphabet : 0 < alphabet)
    (A : Finset (Fin n → Fin alphabet)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V A) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin alphabet))) ∧
      ¬ ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n),
        Subspace.IsContained V (uncovered A 𝒱) := by
  classical
  letI : Fintype (Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n)) :=
    Fintype.ofInjective (fun V ↦ V.idxFun) fun V W h ↦ by
      cases V
      cases W
      cases h
      rfl
  let P : Set (Finset (Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n))) :=
    {𝒱 | (∀ V ∈ 𝒱, Subspace.IsContained V A) ∧
      (𝒱 : Set (Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n))).PairwiseDisjoint
        fun V ↦ (Subspace.range V : Set (Fin n → Fin alphabet))}
  have hPfinite : P.Finite := Set.finite_univ.subset fun _ _ ↦ Set.mem_univ _
  obtain ⟨𝒱, hP, hmax⟩ := hPfinite.exists_maximalFor Finset.card P ⟨∅, by simp [P]⟩
  refine ⟨𝒱, 𝒱.finite_toSet, hP.1, hP.2, ?_⟩
  rintro ⟨V, hV⟩
  have hVnot : V ∉ 𝒱 := by
    intro hVmem
    let x : Fin dimension → Fin alphabet := fun _ ↦ ⟨0, halphabet⟩
    have hx := hV x
    simp only [uncovered, Finset.mem_filter] at hx
    exact hx.2 V hVmem (Subspace.mem_range.mpr ⟨x, rfl⟩)
  apply Nat.not_succ_le_self 𝒱.card
  change 𝒱.card + 1 ≤ 𝒱.card
  rw [← Finset.card_insert_of_notMem hVnot]
  apply hmax
  · simp only [P]
    refine ⟨?_, ?_⟩
    · intro W hW
      simp only [Finset.mem_insert] at hW
      rcases hW with rfl | hW
      · intro x
        have hx := hV x
        simp only [uncovered, Finset.mem_filter] at hx
        exact hx.1
      · exact hP.1 W hW
    · rw [Finset.coe_insert]
      refine hP.2.insert_of_notMem hVnot ?_
      intro W hW
      rw [Set.disjoint_left]
      intro w hwV hwW
      obtain ⟨x, hx⟩ := Subspace.mem_range.mp hwV
      have hx' := hV x
      simp only [uncovered, Finset.mem_filter] at hx'
      exact hx'.2 W hW (hx.symm ▸ hwW)
  · exact Finset.card_le_card (Finset.subset_insert _ _)

/-- Finite-stage block packing gives one exact sufficient dimension for one-family tiling. -/
lemma exists_tilingSufficient_dimension (k m : ℕ) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (_hβ₁ : β ≤ 1) :
    ∃ N, TilingSufficient k m β N := by
  by_cases hβ : β < 1
  · obtain ⟨N, hN⟩ :=
      Subspace.exists_uniformFibersFinSufficient (k + 1) m hm hβ₀ hβ
    refine ⟨N, ?_⟩
    intro _i D _hD hDβ
    obtain ⟨𝒱, hfinite, hcontained, hpairwise, hmaximal⟩ :=
      exists_maximal_subspace_packing (by omega) D
    refine ⟨𝒱, hfinite, hcontained, hpairwise, ?_⟩
    by_contra huncovered
    have hdense :
        β < ((uncovered D 𝒱).dens : ℝ) := by
      have := le_of_not_gt huncovered
      linarith
    obtain ⟨V, hV⟩ :=
      exists_subspace_of_uniformFibersFinSufficient hβ₀ hN (uncovered D 𝒱) hdense
    exact hmaximal ⟨V, hV⟩
  · refine ⟨m, ?_⟩
    intro _i D _hD hDβ
    have hD₁ : (D.dens : ℝ) ≤ 1 := by
      exact_mod_cast Finset.dens_le_one (s := D)
    linarith

/-- A tiling in every fixed extra-coordinate section combines to a tiling of the full cube. -/
private lemma tilingSufficient_mono {k m N n : ℕ} {β : ℝ}
    (hN : TilingSufficient k m β N) (hNn : N ≤ n) :
    TilingSufficient k m β n := by
  classical
  intro i D hD hDβ
  let r := n - N
  have hNr : N + r = n := Nat.add_sub_of_le hNn
  let e : Fin r ⊕ Fin N ≃ Fin n :=
    (Equiv.sumComm (Fin r) (Fin N)).trans <| finSumFinEquiv.trans (finCongr hNr)
  let wordEquiv :=
    e.arrowCongr (Equiv.refl (Fin (k + 1)))
  let D' := D.map wordEquiv.symm.toEmbedding
  let slice := fun z : Fin r → Fin (k + 1) ↦ fiber D' z
  have hslice (z : Fin r → Fin (k + 1)) :
      IsInsensitive i.castSucc (Fin.last k) (slice z) := by
    intro x y hxy
    simp only [slice, mem_fiber, D', Finset.mem_map_equiv]
    apply hD
    intro a hai hal c
    cases hc : e.symm c with
    | inl j =>
        simp [wordEquiv, Equiv.arrowCongr, DensityHalesJewett.concat, hc]
    | inr j =>
        simpa [wordEquiv, Equiv.arrowCongr, DensityHalesJewett.concat, hc] using
          hxy a hai hal j
  have existsLocal (z : Fin r → Fin (k + 1)) :
      ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N)),
        𝒱.Finite ∧
        (∀ V ∈ 𝒱, Subspace.IsContained V (slice z)) ∧
        (𝒱.PairwiseDisjoint fun V ↦
          (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
        ((uncovered (slice z) 𝒱).dens : ℝ) < 2 * β := by
    by_cases hz : 2 * β ≤ ((slice z).dens : ℝ)
    · exact hN i (slice z) (hslice z) hz
    · refine ⟨∅, Set.finite_empty, ?_, Set.pairwiseDisjoint_empty, ?_⟩
      · simp
      · have huncovered : uncovered (slice z)
            (∅ : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N))) =
              slice z := by
          simp [uncovered]
        rw [huncovered]
        exact lt_of_not_ge hz
  let tiles := fun z : Fin r → Fin (k + 1) ↦ Classical.choose (existsLocal z)
  have hlocal (z : Fin r → Fin (k + 1)) :
      (tiles z).Finite ∧
      (∀ V ∈ tiles z, Subspace.IsContained V (slice z)) ∧
      ((tiles z).PairwiseDisjoint fun V ↦
        (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
      ((uncovered (slice z) (tiles z)).dens : ℝ) < 2 * β :=
    Classical.choose_spec (existsLocal z)
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ z, padExtraSubspace e z '' tiles z
  refine ⟨global, ?_, ?_, ?_, ?_⟩
  · dsimp only [global]
    exact Set.finite_iUnion fun z ↦
      (hlocal z).1.image (padExtraSubspace e z)
  · intro U hU x
    simp only [global, Set.mem_iUnion, Set.mem_image] at hU
    obtain ⟨z, V, hV, rfl⟩ := hU
    simp only [padExtraSubspace_apply]
    have hx := (hlocal z).2.1 V hV x
    simpa [slice, D', Finset.mem_map_equiv, wordEquiv, Equiv.arrowCongr] using hx
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    simp only [global, Set.mem_iUnion, Set.mem_image] at hU hU'
    obtain ⟨z, V, hV, rfl⟩ := hU
    obtain ⟨z', V', hV', rfl⟩ := hU'
    obtain ⟨w, hw, hw'⟩ := hcommon
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
    have hzx :
        DensityHalesJewett.concat z (V x) =
          DensityHalesJewett.concat z' (V' x') := by
      funext c
      have hc := congrFun (hx.trans hx'.symm) (e c)
      simpa only [padExtraSubspace_apply, Function.comp_apply,
        Equiv.symm_apply_apply] using hc
    have hzz : z = z' := by
      funext j
      exact congrFun hzx (Sum.inl j)
    subst z'
    apply congrArg (padExtraSubspace e z)
    apply Set.pairwiseDisjoint_iff.mp (hlocal z).2.2.1 hV hV'
    refine ⟨V x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨x', ?_⟩⟩
    exact funext fun j ↦ (congrFun hzx (Sum.inr j)).symm
  · let E := (uncovered D global).map wordEquiv.symm.toEmbedding
    have hfiber (z : Fin r → Fin (k + 1)) :
        fiber E z = uncovered (slice z) (tiles z) := by
      ext y
      simp only [E, mem_fiber, Finset.mem_map_equiv, uncovered,
        Finset.mem_filter, slice, D', global]
      constructor
      · rintro ⟨hyD, hyfree⟩
        refine ⟨hyD, ?_⟩
        intro V hV hyV
        apply hyfree (padExtraSubspace e z V)
        · exact Set.mem_iUnion_of_mem z <| Set.mem_image_of_mem _ hV
        · obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyV
          exact Subspace.mem_range.mpr ⟨x, by
            simp [padExtraSubspace_apply, wordEquiv, Equiv.arrowCongr, hx]⟩
      · rintro ⟨hyD, hyfree⟩
        refine ⟨hyD, ?_⟩
        intro U hU hyU
        simp only [Set.mem_iUnion, Set.mem_image] at hU
        obtain ⟨z', V, hV, rfl⟩ := hU
        obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyU
        have hconcat :
            DensityHalesJewett.concat z y =
              DensityHalesJewett.concat z' (V x) := by
          apply wordEquiv.injective
          simpa [padExtraSubspace_apply, wordEquiv, Equiv.arrowCongr] using hx.symm
        have hzz : z = z' := by
          funext j
          exact congrFun hconcat (Sum.inl j)
        subst z'
        apply hyfree V hV
        exact Subspace.mem_range.mpr ⟨x,
          funext fun j ↦ (congrFun hconcat (Sum.inr j)).symm⟩
    have hEdens :
        (E.dens : ℝ) = ((uncovered D global).dens : ℝ) := by
      simp only [E, Finset.dens_map_equiv]
    rw [← hEdens, ← average_density_fiber]
    apply Finset.expect_lt
    · intro z _
      rw [hfiber]
      exact (hlocal z).2.2.2.le
    · let z : Fin r → Fin (k + 1) := fun _ ↦ 0
      refine ⟨z, Finset.mem_univ z, ?_⟩
      rw [hfiber]
      exact (hlocal z).2.2.2

/-- One-family tiling sufficiency is upward closed after padding with unused final coordinates. -/
lemma exists_eventually_tilingSufficient (k m : ℕ) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, ∀ n ≥ N, TilingSufficient k m β n := by
  obtain ⟨N, hN⟩ := exists_tilingSufficient_dimension k m hm hβ₀ hβ₁
  exact ⟨N, fun _n hn ↦ tilingSufficient_mono hN hn⟩

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

/-- One indexed insensitive family is exactly the one-family tiling statement. -/
private lemma intersectionTilingSufficient_one {k m n : ℕ} {β : ℝ}
    (h : TilingSufficient k m β n) :
    IntersectionTilingSufficient k 1 m β n := by
  intro _ hrk D hD hDβ
  have hintersection : intersection D = D 0 := by
    ext x
    simp only [mem_intersection]
    exact ⟨fun hx ↦ hx 0, fun hx i ↦ by simpa only [Fin.eq_zero i] using hx⟩
  have hsensitive :
      IsInsensitive (Fin.castLE hrk 0).castSucc (Fin.last k) (D 0) :=
    hD 0
  obtain ⟨𝒱, hfinite, hcontained, hpairwise, huncovered⟩ :=
    h (Fin.castLE hrk 0) (D 0) hsensitive (by
      rw [hintersection] at hDβ
      norm_num at hDβ ⊢
      exact hDβ)
  refine ⟨𝒱, hfinite, ?_, hpairwise, ?_⟩
  · simpa only [hintersection] using hcontained
  · rw [hintersection]
    norm_num
    exact huncovered

/-- The two-stage outer/inner packing step for adding one insensitive family. -/
private lemma extend_intersection_tiling {k r m M n : ℕ}
    (hr₀ : 1 ≤ r) (hrk : r + 1 ≤ k) {β : ℝ} (hβ₀ : 0 < β)
    (houter : IntersectionTilingSufficient k r M β n)
    (hinner : TilingSufficient k m β M) :
    IntersectionTilingSufficient k (r + 1) m β n := by
  intro _ hrk' D hD hDβ
  let D₀ : Fin r → Finset (Fin n → Fin (k + 1)) := fun i ↦
    D (Fin.castSucc i)
  have hsubset : intersection D ⊆ intersection D₀ := by
    intro x hx
    rw [mem_intersection] at hx ⊢
    intro i
    simpa only [D₀] using hx (Fin.castSucc i)
  have hD₀ (i : Fin r) :
      IsInsensitive (Fin.castLE (by omega) i).castSucc (Fin.last k) (D₀ i) := by
    have hindex : Fin.castLE hrk' (Fin.castSucc i) = Fin.castLE (by omega) i := by
      apply Fin.ext
      rfl
    rw [← hindex]
    simpa only [D₀] using hD (Fin.castSucc i)
  obtain ⟨𝒱, hfinite, hcontained, hpairwise, huncovered⟩ :=
    houter hr₀ (by omega) D₀ hD₀ (by
        refine (show 2 * r * β ≤ 2 * (r + 1) * β by nlinarith).trans ?_
        have hdens : ((intersection D).dens : ℝ) ≤ ((intersection D₀).dens : ℝ) := by
          exact_mod_cast Finset.dens_mono hsubset
        convert hDβ.trans hdens using 1
        norm_num)
  let iLast : Fin k := ⟨r, by omega⟩
  let DLast := D (Fin.last r)
  have hLast : IsInsensitive iLast.castSucc (Fin.last k) DLast := by
    convert hD (Fin.last r) using 1
    simp only [iLast, Fin.castLE, Fin.last, Fin.castSucc]
  let pullback := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    parameterPreimage V DLast
  have hPullback (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      IsInsensitive iLast.castSucc (Fin.last k) (pullback V) :=
    parameterPreimage_isInsensitive V DLast hLast
  have existsInner (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      ∃ 𝒲 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M)),
        𝒲.Finite ∧
        (∀ W ∈ 𝒲, Subspace.IsContained W (pullback V)) ∧
        (𝒲.PairwiseDisjoint fun W ↦
          (Subspace.range W : Set (Fin M → Fin (k + 1)))) ∧
        ((uncovered (pullback V) 𝒲).dens : ℝ) < 2 * β := by
    by_cases hV : 2 * β ≤ ((pullback V).dens : ℝ)
    · exact hinner iLast (pullback V) (hPullback V) hV
    · refine ⟨∅, Set.finite_empty, ?_, Set.pairwiseDisjoint_empty, ?_⟩
      · simp
      · have huncovered : uncovered (pullback V)
            (∅ : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M))) = pullback V := by
          simp [uncovered]
        rw [huncovered]
        exact lt_of_not_ge hV
  sorry

/-- Induction on the number of insensitive families gives one exact sufficient intersection-tiling
dimension. -/
lemma exists_intersectionTilingSufficient_dimension (k r m : ℕ)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, IntersectionTilingSufficient k r m β N := by
  induction r using Nat.strong_induction_on generalizing m with
  | h r ih =>
      obtain rfl | hr := r
      · omega
      obtain rfl | s := hr
      · obtain ⟨N, hN⟩ := exists_tilingSufficient_dimension k m hm hβ₀ hβ₁
        exact ⟨N, intersectionTilingSufficient_one hN⟩
      · let M := max 1 (tilingBound k m β)
        have hM : 1 ≤ M := le_max_left _ _
        obtain ⟨N, houter⟩ :=
          ih (s + 1) (by omega) M (by omega) (by omega) hM
        have hinner : TilingSufficient k m β M :=
          tilingBound_spec k m M hm hβ₀ hβ₁ (le_max_right _ _)
        exact ⟨N, extend_intersection_tiling (by omega) (by omega) hβ₀ houter hinner⟩

/-- Exact intersection-tiling sufficiency transports to every larger coordinate dimension. -/
private lemma intersectionTilingSufficient_mono {k r m N n : ℕ} {β : ℝ}
    (hN : IntersectionTilingSufficient k r m β N) (hNn : N ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  classical
  intro hr₀ hrk D hD hDβ
  let q := n - N
  have hNq : N + q = n := Nat.add_sub_of_le hNn
  let e : Fin q ⊕ Fin N ≃ Fin n :=
    (Equiv.sumComm (Fin q) (Fin N)).trans <| finSumFinEquiv.trans (finCongr hNq)
  let wordEquiv := e.arrowCongr (Equiv.refl (Fin (k + 1)))
  let D' := fun i ↦ (D i).map wordEquiv.symm.toEmbedding
  let slice := fun z : Fin q → Fin (k + 1) ↦ fun i ↦ fiber (D' i) z
  have hslice (z : Fin q → Fin (k + 1)) (i : Fin r) :
      IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (slice z i) := by
    intro x y hxy
    simp only [slice, mem_fiber, D', Finset.mem_map_equiv]
    apply hD i
    intro a hai hal c
    cases hc : e.symm c with
    | inl j =>
        simp [wordEquiv, Equiv.arrowCongr, DensityHalesJewett.concat, hc]
    | inr j =>
        simpa [wordEquiv, Equiv.arrowCongr, DensityHalesJewett.concat, hc] using
          hxy a hai hal j
  let I := intersection D
  let I' := I.map wordEquiv.symm.toEmbedding
  have hIdens : (I'.dens : ℝ) = (I.dens : ℝ) := by
    simp only [I', Finset.dens_map_equiv]
  have hfiberI (z : Fin q → Fin (k + 1)) :
      fiber I' z = intersection (slice z) := by
    ext y
    simp only [mem_fiber, Finset.mem_map_equiv, I', I, mem_intersection, slice, D',
      Equiv.symm_symm]
  have existsLocal (z : Fin q → Fin (k + 1)) :
      ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N)),
        𝒱.Finite ∧
        (∀ V ∈ 𝒱, Subspace.IsContained V (intersection (slice z))) ∧
        (𝒱.PairwiseDisjoint fun V ↦
          (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
        ((uncovered (intersection (slice z)) 𝒱).dens : ℝ) < 2 * r * β := by
    by_cases hz : 2 * r * β ≤ ((intersection (slice z)).dens : ℝ)
    · exact hN hr₀ hrk (slice z) (hslice z) hz
    · refine ⟨∅, Set.finite_empty, ?_, Set.pairwiseDisjoint_empty, ?_⟩
      · simp
      · have huncovered : uncovered (intersection (slice z))
            (∅ : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N))) =
              intersection (slice z) := by
          simp [uncovered]
        rw [huncovered]
        exact lt_of_not_ge hz
  let tiles := fun z : Fin q → Fin (k + 1) ↦ Classical.choose (existsLocal z)
  have hlocal (z : Fin q → Fin (k + 1)) :
      (tiles z).Finite ∧
      (∀ V ∈ tiles z, Subspace.IsContained V (intersection (slice z))) ∧
      ((tiles z).PairwiseDisjoint fun V ↦
        (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
      ((uncovered (intersection (slice z)) (tiles z)).dens : ℝ) < 2 * r * β :=
    Classical.choose_spec (existsLocal z)
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ z, padExtraSubspace e z '' tiles z
  refine ⟨global, ?_, ?_, ?_, ?_⟩
  · dsimp only [global]
    exact Set.finite_iUnion fun z ↦
      (hlocal z).1.image (padExtraSubspace e z)
  · intro U hU x
    simp only [global, Set.mem_iUnion, Set.mem_image] at hU
    obtain ⟨z, V, hV, rfl⟩ := hU
    simp only [padExtraSubspace_apply]
    have hx := (hlocal z).2.1 V hV x
    rw [← hfiberI z] at hx
    rw [mem_fiber] at hx
    simp only [I', Finset.mem_map_equiv, Equiv.symm_symm] at hx
    have hword : wordEquiv (DensityHalesJewett.concat z (V x)) =
        DensityHalesJewett.concat z (V x) ∘ e.symm := by
      rfl
    rw [hword] at hx
    simpa only [I, mem_intersection] using hx
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    simp only [global, Set.mem_iUnion, Set.mem_image] at hU hU'
    obtain ⟨z, V, hV, rfl⟩ := hU
    obtain ⟨z', V', hV', rfl⟩ := hU'
    obtain ⟨w, hw, hw'⟩ := hcommon
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
    have hzx :
        DensityHalesJewett.concat z (V x) =
          DensityHalesJewett.concat z' (V' x') := by
      funext c
      have hc := congrFun (hx.trans hx'.symm) (e c)
      simpa only [padExtraSubspace_apply, Function.comp_apply,
        Equiv.symm_apply_apply] using hc
    have hzz : z = z' := by
      funext j
      exact congrFun hzx (Sum.inl j)
    subst z'
    apply congrArg (padExtraSubspace e z)
    apply Set.pairwiseDisjoint_iff.mp (hlocal z).2.2.1 hV hV'
    refine ⟨V x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨x', ?_⟩⟩
    exact funext fun j ↦ (congrFun hzx (Sum.inr j)).symm
  · let E := (uncovered I global).map wordEquiv.symm.toEmbedding
    have hfiber (z : Fin q → Fin (k + 1)) :
        fiber E z = uncovered (intersection (slice z)) (tiles z) := by
      ext y
      simp only [E, mem_fiber, Finset.mem_map_equiv, uncovered,
        Finset.mem_filter, global]
      constructor
      · rintro ⟨hyD, hyfree⟩
        refine ⟨?_, ?_⟩
        · rw [← hfiberI z]
          simp only [mem_fiber, I', Finset.mem_map_equiv, Equiv.symm_symm]
          exact hyD
        · intro V hV hyV
          apply hyfree (padExtraSubspace e z V)
          · exact Set.mem_iUnion_of_mem z <| Set.mem_image_of_mem _ hV
          · obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyV
            exact Subspace.mem_range.mpr ⟨x, by
              simp [padExtraSubspace_apply, wordEquiv, Equiv.arrowCongr, hx]⟩
      · rintro ⟨hyD, hyfree⟩
        refine ⟨?_, ?_⟩
        · rw [← hfiberI z] at hyD
          rw [mem_fiber] at hyD
          simpa only [I', Finset.mem_map_equiv, Equiv.symm_symm] using hyD
        · intro U hU hyU
          simp only [Set.mem_iUnion, Set.mem_image] at hU
          obtain ⟨z', V, hV, rfl⟩ := hU
          obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyU
          have hconcat :
              DensityHalesJewett.concat z y =
                DensityHalesJewett.concat z' (V x) := by
            apply wordEquiv.injective
            simpa [padExtraSubspace_apply, wordEquiv, Equiv.arrowCongr] using hx.symm
          have hzz : z = z' := by
            funext j
            exact congrFun hconcat (Sum.inl j)
          subst z'
          apply hyfree V hV
          exact Subspace.mem_range.mpr ⟨x,
            funext fun j ↦ (congrFun hconcat (Sum.inr j)).symm⟩
    have hEdens :
        (E.dens : ℝ) = ((uncovered I global).dens : ℝ) := by
      simp only [E, Finset.dens_map_equiv]
    rw [← hEdens, ← average_density_fiber]
    apply Finset.expect_lt
    · intro z _
      rw [hfiber]
      exact (hlocal z).2.2.2.le
    · let z : Fin q → Fin (k + 1) := fun _ ↦ 0
      refine ⟨z, Finset.mem_univ z, ?_⟩
      rw [hfiber]
      exact (hlocal z).2.2.2

/-- Intersection-tiling sufficiency is upward closed after padding with unused final
coordinates. -/
lemma exists_eventually_intersectionTilingSufficient (k r m : ℕ)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, ∀ n ≥ N, IntersectionTilingSufficient k r m β n := by
  obtain ⟨N, hN⟩ :=
    exists_intersectionTilingSufficient_dimension k r m hr₀ hrk hm hβ₀ hβ₁
  exact ⟨N, fun _n hn ↦ intersectionTilingSufficient_mono hN hn⟩

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

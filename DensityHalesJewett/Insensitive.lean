/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.UniformFibers
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
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
open scoped BigOperators

namespace DensityHalesJewett

/-- Two words are equivalent after freely interchanging the letters `i` and `j`. -/
def InsensitiveEquiv {α ι : Type*} (i j : α) (x y : ι → α) : Prop :=
  ∀ a, a ≠ i → a ≠ j → ∀ c, (x c = a ↔ y c = a)

/-- Membership in an `(i,j)`-insensitive family is constant on insensitive-equivalence classes. -/
def IsInsensitive {α ι : Type*} (i j : α) (D : Finset (ι → α)) : Prop :=
  ∀ ⦃x y⦄, InsensitiveEquiv i j x y → (x ∈ D ↔ y ∈ D)

/-- Transport a word family along an equivalence of coordinate types. -/
def transportWords {α ι ι' : Type*}
    (e : ι ≃ ι') (D : Finset (ι → α)) : Finset (ι' → α) :=
  D.map ((e.arrowCongr (Equiv.refl α)).toEmbedding)

@[simp]
lemma mem_transportWords {α ι ι' : Type*}
    {e : ι ≃ ι'} {D : Finset (ι → α)} {w : ι' → α} :
    w ∈ transportWords e D ↔ w ∘ e ∈ D := by
  rw [transportWords, Finset.mem_map_equiv]
  rfl

@[simp]
lemma dens_transportWords {α ι ι' : Type*} [Fintype (ι → α)] [Fintype (ι' → α)]
    (e : ι ≃ ι') (D : Finset (ι → α)) : (transportWords e D).dens = D.dens := by
  rw [transportWords, Finset.dens_map_equiv]

/-- Fix the coordinates outside a designated block, keeping a subspace on the block. -/
def transportSubspace {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) : Combinatorics.Subspace η α ι where
  idxFun c := Sum.elim (fun a ↦ Sum.inl (z a)) V.idxFun (e c)
  proper x := by
    obtain ⟨c, hc⟩ := V.proper x
    exact ⟨e.symm (Sum.inr c), by simp only [Equiv.apply_symm_apply, Sum.elim_inr, hc]⟩

@[simp]
lemma transportSubspace_apply {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) (x : η → α) :
    transportSubspace e z V x = DensityHalesJewett.concat z (V x) ∘ e := by
  funext c
  simp only [Combinatorics.Subspace.coe_apply, transportSubspace, Function.comp_apply]
  cases e c with
  | inl a => simp only [Sum.elim_inl, DensityHalesJewett.concat_apply_inl, id_eq]
  | inr c =>
      rw [Sum.elim_inr, DensityHalesJewett.concat_apply_inr, Combinatorics.Subspace.coe_apply]

namespace IsInsensitive

/-- Reindexing coordinates preserves insensitivity. -/
lemma reindex {α ι ι' : Type*}
    {i j : α} {D : Finset (ι → α)} (e : ι ≃ ι') (hD : IsInsensitive i j D) :
    IsInsensitive i j (DensityHalesJewett.transportWords e D) := by
  intro x y hxy
  simp only [mem_transportWords]
  refine hD fun a hai haj c ↦ ?_
  exact hxy a hai haj (e c)

/-- Fixing a prefix of coordinates preserves insensitivity of the remaining section. -/
lemma fiberSection {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : IsInsensitive i j D) (v : ι → α) :
    IsInsensitive i j (DensityHalesJewett.fiber D v) := by
  intro x y hxy
  simp only [mem_fiber]
  refine hD fun a hai haj c ↦ ?_
  cases c with
  | inl c => simp only [DensityHalesJewett.concat_apply_inl]
  | inr c => exact hxy a hai haj c

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

/-- Differences preserve insensitivity. -/
lemma sdiff {α ι : Type*} [DecidableEq (ι → α)]
    {i j : α} {D E : Finset (ι → α)} (hD : IsInsensitive i j D)
    (hE : IsInsensitive i j E) : IsInsensitive i j (D \ E) := by
  intro x y hxy
  simp only [Finset.mem_sdiff]
  rw [hD hxy, hE hxy]

/-- Insensitive-equivalent prefixes have the same section. -/
lemma fiber_congr {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : IsInsensitive i j D) {v w : ι → α}
    (hvw : InsensitiveEquiv i j v w) :
    DensityHalesJewett.fiber D v = DensityHalesJewett.fiber D w := by
  ext y
  simp only [mem_fiber]
  refine hD fun a hai haj c ↦ ?_
  cases c with
  | inl c => exact hvw a hai haj c
  | inr c => simp only [DensityHalesJewett.concat_apply_inr]

end IsInsensitive

/-- Regrouping the coordinates of a word with a fixed prefix and a split tail. -/
private lemma concat_comp_regroup {α ω ν ν₁ ν₂ : Type*} (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    DensityHalesJewett.concat (DensityHalesJewett.concat u r) x ∘
        (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm) =
      DensityHalesJewett.concat u (DensityHalesJewett.concat r x ∘ s) := by
  funext c
  cases c with
  | inl a => simp [Equiv.sumAssoc]
  | inr n => cases hn : s n <;> simp [Equiv.sumAssoc, hn]

/-- The same regrouping stated after a coordinate splitting of the ambient type. -/
private lemma concat_comp_regroup_trans {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν)
    (s : ν ≃ ν₁ ⊕ ν₂) (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    DensityHalesJewett.concat (DensityHalesJewett.concat u r) x ∘
        (e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)) =
      DensityHalesJewett.concat u (DensityHalesJewett.concat r x ∘ s) ∘ e := by
  rw [← concat_comp_regroup s u r x]
  rfl

/-- Sections over the last block of a split tail are sections of sections. -/
private lemma fiber_transportWords_regroup {α ι ω ν ν₁ ν₂ : Type*}
    [Fintype α] [DecidableEq α] [Fintype ω]
    [Fintype ν] [DecidableEq ν] [Fintype ν₁] [Fintype ν₂] [DecidableEq ν₂]
    (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂) (U : Finset (ι → α)) (u : ω → α) (r : ν₁ → α) :
    DensityHalesJewett.fiber
        (transportWords (e.trans (((Equiv.refl ω).sumCongr s).trans
          (Equiv.sumAssoc ω ν₁ ν₂).symm)) U) (DensityHalesJewett.concat u r) =
      DensityHalesJewett.fiber
        (transportWords s (DensityHalesJewett.fiber (transportWords e U) u)) r := by
  ext x
  simp only [mem_fiber, mem_transportWords, concat_comp_regroup_trans]

/-- A word is the concatenation of its parts along a coordinate splitting. -/
private lemma eq_concat_parts {α ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (w : ι → α) :
    DensityHalesJewett.concat (fun a ↦ w (e.symm (Sum.inl a)))
        (fun n ↦ w (e.symm (Sum.inr n))) ∘ e = w := by
  funext c
  cases hc : e c with
  | inl a =>
      rw [Function.comp_apply, hc, DensityHalesJewett.concat_apply_inl, ← hc,
        Equiv.symm_apply_apply]
  | inr n =>
      rw [Function.comp_apply, hc, DensityHalesJewett.concat_apply_inr, ← hc,
        Equiv.symm_apply_apply]

/-- Sections commute with set difference. -/
private lemma fiber_transportWords_sdiff {α ι ω ν : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [Fintype ω]
    [Fintype ν] [DecidableEq ν]
    (e : ι ≃ ω ⊕ ν) (A B : Finset (ι → α)) (v : ω → α) :
    DensityHalesJewett.fiber (transportWords e (A \ B)) v =
      DensityHalesJewett.fiber (transportWords e A) v \
        DensityHalesJewett.fiber (transportWords e B) v := by
  ext y
  simp only [Finset.mem_sdiff, mem_fiber, mem_transportWords]

/-- Removing a subset from a family subtracts its density. -/
private lemma dens_sdiff_of_subset {X : Type*} [Fintype X] [DecidableEq X] {A B : Finset X}
    (h : B ⊆ A) : (((A \ B).dens : ℝ)) = (A.dens : ℝ) - (B.dens : ℝ) := by
  rw [Finset.nnratCast_dens, Finset.nnratCast_dens, Finset.nnratCast_dens,
    Finset.card_sdiff_of_subset h, Nat.cast_sub (Finset.card_le_card h), sub_div]

/-- A nonempty family occupies at least one point of the ambient cube. -/
private lemma one_div_card_le_dens {X : Type*} [Fintype X] {A : Finset X} (h : A.Nonempty) :
    1 / (Fintype.card X : ℝ) ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  gcongr
  exact_mod_cast h.card_pos

/-- An insensitive family that is dense in a large enough block contains a full subspace: the
restricted-alphabet subspace lemma supplies the `Fin k`-restricted range, and insensitivity
upgrades containment to the whole parameter cube. -/
lemma exists_isContained_of_insensitive {k m b : ℕ} (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    (i : Fin k) {β : ℝ} (hβ : 0 < β) (hb : Subspace.restrictAlphabetBound k m β ≤ b)
    (E : Finset (Fin b → Fin (k + 1)))
    (hE : IsInsensitive i.castSucc (Fin.last k) E) (hdens : β ≤ (E.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b), Subspace.IsContained V E := by
  obtain ⟨V, hV⟩ :=
    Subspace.exists_restrictAlphabet_subset hDHJ m hm β hβ b hb E
      (by
        have := Subspace.card_le_of_density_le (k := k + 1) (Nat.succ_pos k) β E hdens
        push_cast at this ⊢
        exact this)
  refine ⟨V, fun x ↦ ?_⟩
  refine (hE fun a hai hal c ↦ ?_).mpr
    (hV (Finset.mem_image.mpr ⟨fun e ↦ if h : x e = Fin.last k then i else (x e).castPred h,
      Finset.mem_univ _, rfl⟩))
  cases hc : V.idxFun c with
  | inl t => simp only [V.apply_inl hc]
  | inr e =>
      simp only [V.apply_inr hc, Function.comp_apply]
      by_cases hx : x e = Fin.last k
      · rw [dif_pos hx, hx, Fin.castSuccEmb_apply]
        exact iff_of_false (fun h ↦ hal h.symm) (fun h ↦ hai h.symm)
      · rw [dif_neg hx, Fin.castSuccEmb_apply, Fin.castSucc_castPred]

/-- A word on a sum of coordinate types is the concatenation of its two parts. -/
private lemma concat_inl_inr {α ω ν : Type*} (z : ω ⊕ ν → α) :
    DensityHalesJewett.concat (fun a ↦ z (Sum.inl a)) (fun n ↦ z (Sum.inr n)) = z := by
  funext c
  cases c <;> rfl

/-- The two block orders describe the same ambient word. -/
private lemma concat_comp_swap {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (y : ν₁ → α) (x : ν₂ → α) :
    DensityHalesJewett.concat (DensityHalesJewett.concat u y) x ∘
        (e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)) =
      DensityHalesJewett.concat (DensityHalesJewett.concat u x) y ∘
        (e.trans (((Equiv.refl ω).sumCongr (s.trans (Equiv.sumComm ν₁ ν₂))).trans
          (Equiv.sumAssoc ω ν₂ ν₁).symm)) := by
  rw [concat_comp_regroup_trans, concat_comp_regroup_trans]
  refine congrArg (· ∘ e) (congrArg (DensityHalesJewett.concat u) ?_)
  funext n
  cases hn : s n <;> simp [hn]

/-- A canonical subspace contained in a family, depending on nothing but the family. -/
noncomputable def pickSubspace {k m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (E : Finset (Fin b → Fin (k + 1))) :
    Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b) := by
  classical
  exact if h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.IsContained V E then Classical.choose h
    else Subspace.repeatInitial (Fin (k + 1)) hm hmb

lemma pickSubspace_isContained {k m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    {E : Finset (Fin b → Fin (k + 1))}
    (h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.IsContained V E) :
    Subspace.IsContained (pickSubspace hm hmb E) E := by
  classical
  rw [pickSubspace, dif_pos h]
  exact Classical.choose_spec h

namespace IsInsensitive

/-- Nothing is covered by an empty family of subspaces. -/
@[simp]
private lemma uncovered_empty {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (D : Finset (ι → α)) :
    uncovered D (∅ : Set (Combinatorics.Subspace η α ι)) = D := by
  simp only [uncovered, Set.mem_empty_iff_false, false_implies, implies_true,
    Finset.filter_true_of_mem]

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

/-- The block density-increment tiling of paper Lemma 12.

The coordinates are split into an already consumed part `ω` and `T` fresh blocks of size `b`. The
invariant is that all sections of the working family over the fresh blocks stay insensitive; each
stage either has already reached uncovered density below `2 * β` or removes disjoint tiles of total
density at least `β / (k + 1) ^ b`, and choosing the local subspace canonically from the section
keeps the invariant for the later blocks. -/
private lemma exists_tiling_of_insensitive_sections {k : ℕ} (i : Fin k) (hDHJ : HasDensityHJ k)
    {m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hb : Subspace.restrictAlphabetBound k m β ≤ b) :
    ∀ T : ℕ, ∀ ι ω : Type, ∀ [Fintype ι] [DecidableEq ι] [Fintype ω],
      ∀ e : ι ≃ ω ⊕ Fin (T * b), ∀ U : Finset (ι → Fin (k + 1)),
        (∀ v : ω → Fin (k + 1),
          IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e U) v)) →
        ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι),
          𝒱.Finite ∧ (∀ V ∈ 𝒱, Subspace.IsContained V U) ∧
          (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (ι → Fin (k + 1)))) ∧
          (((uncovered U 𝒱).dens : ℝ) < 2 * β ∨
            ((uncovered U 𝒱).dens : ℝ) + T * (β / ((k : ℝ) + 1) ^ b) ≤ (U.dens : ℝ)) := by
  classical
  intro T
  induction T with
  | zero =>
      intro ι ω _ _ _ e U _
      refine ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty, Or.inr ?_⟩
      simp only [uncovered_empty, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ S ih =>
      intro ι ω _ _ _ e U hins
      by_cases hU : (U.dens : ℝ) < 2 * β
      · exact ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty, Or.inl (by simpa using hU)⟩
      push Not at hU
      -- split the fresh blocks into the leading ones and the block consumed by this stage
      have hsplit : S * b + b = (S + 1) * b := by ring
      set s : Fin ((S + 1) * b) ≃ Fin (S * b) ⊕ Fin b :=
        (finSumFinEquiv.trans (finCongr hsplit)).symm with hs
      set e₁ : ι ≃ (ω ⊕ Fin (S * b)) ⊕ Fin b :=
        e.trans (((Equiv.refl ω).sumCongr s).trans
          (Equiv.sumAssoc ω (Fin (S * b)) (Fin b)).symm) with he₁
      set e₂ : ι ≃ (ω ⊕ Fin b) ⊕ Fin (S * b) :=
        e.trans (((Equiv.refl ω).sumCongr (s.trans (Equiv.sumComm (Fin (S * b)) (Fin b)))).trans
          (Equiv.sumAssoc ω (Fin b) (Fin (S * b))).symm) with he₂
      set B : (ω ⊕ Fin (S * b) → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)) :=
        fun z ↦ fiber (transportWords e₁ U) z with hBdef
      have hB (u : ω → Fin (k + 1)) (r : Fin (S * b) → Fin (k + 1)) :
          B (concat u r) = fiber (transportWords s (fiber (transportWords e U) u)) r :=
        fiber_transportWords_regroup e s U u r
      have hBins (z : ω ⊕ Fin (S * b) → Fin (k + 1)) :
          IsInsensitive i.castSucc (Fin.last k) (B z) := by
        rw [← concat_inl_inr z, hB]
        exact fiberSection (reindex s (hins _)) _
      -- the blocks above which the working family is dense
      have havg : (𝔼 z : (ω ⊕ Fin (S * b) → Fin (k + 1)), ((B z).dens : ℝ)) = (U.dens : ℝ) := by
        simp only [hBdef]
        rw [average_density_fiber, dens_transportWords]
      have hgood :
          β ≤ ((Finset.univ.filter fun z : ω ⊕ Fin (S * b) → Fin (k + 1) ↦
            β ≤ ((B z).dens : ℝ)).dens : ℝ) := by
        refine le_trans ?_ (density_ge_threshold (fun z ↦ ((B z).dens : ℝ)) (2 * β) β
          (fun _ ↦ by positivity) (fun z ↦ by exact_mod_cast Finset.dens_le_one (s := B z))
          hβ₀.le (by linarith) (by rw [havg]; exact hU))
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      set good : Finset (ω ⊕ Fin (S * b) → Fin (k + 1)) :=
        Finset.univ.filter fun z ↦ β ≤ ((B z).dens : ℝ) with hgooddef
      -- the local subspaces chosen canonically from the sections
      set tile : (ω ⊕ Fin (S * b) → Fin (k + 1)) →
          Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι :=
        fun z ↦ transportSubspace e₁ z (pickSubspace hm hmb (B z)) with htiledef
      have hpick (z : ω ⊕ Fin (S * b) → Fin (k + 1)) (hz : z ∈ good) :
          Subspace.IsContained (pickSubspace hm hmb (B z)) (B z) :=
        pickSubspace_isContained hm hmb
          (exists_isContained_of_insensitive hDHJ hm i hβ₀ hb (B z) (hBins z)
            (by simpa only [hgooddef, Finset.mem_filter, Finset.mem_univ, true_and] using hz))
      -- the part of the working family removed at this stage
      set R : Finset (ι → Fin (k + 1)) := U.filter (fun w ↦
        (fun a ↦ w (e₁.symm (Sum.inl a))) ∈ good ∧
          (fun j ↦ w (e₁.symm (Sum.inr j))) ∈
            Subspace.range (pickSubspace hm hmb (B (fun a ↦ w (e₁.symm (Sum.inl a))))))
        with hRdef
      have hRU : R ⊆ U := Finset.filter_subset _ _
      have htileR (z : ω ⊕ Fin (S * b) → Fin (k + 1)) (hz : z ∈ good)
          (x : Fin m → Fin (k + 1)) : tile z x ∈ R := by
        have hmemU : tile z x ∈ U := by
          have hx := hpick z hz x
          rw [hBdef, mem_fiber, mem_transportWords] at hx
          simpa only [htiledef, transportSubspace_apply] using hx
        have hparts : (fun a ↦ tile z x (e₁.symm (Sum.inl a))) = z := by
          funext a
          simp only [htiledef, transportSubspace_apply, Function.comp_apply,
            Equiv.apply_symm_apply, concat_apply_inl]
        rw [hRdef, Finset.mem_filter]
        refine ⟨hmemU, by rw [hparts]; exact hz, ?_⟩
        rw [hparts]
        refine Subspace.mem_range.mpr ⟨x, ?_⟩
        funext j
        simp only [htiledef, transportSubspace_apply, Function.comp_apply,
          Equiv.apply_symm_apply, concat_apply_inr]
      have hRtile (w : ι → Fin (k + 1)) (hw : w ∈ R) :
          ∃ z ∈ good, w ∈ Subspace.range (tile z) := by
        rw [hRdef, Finset.mem_filter] at hw
        obtain ⟨_, hz, hrange⟩ := hw
        obtain ⟨x, hx⟩ := Subspace.mem_range.mp hrange
        refine ⟨_, hz, Subspace.mem_range.mpr ⟨x, ?_⟩⟩
        rw [htiledef, transportSubspace_apply, hx]
        exact eq_concat_parts e₁ w
      -- the removed part is quantitatively large
      have hdensR : β / ((k : ℝ) + 1) ^ b ≤ (R.dens : ℝ) := by
        have hcard : (Fintype.card (Fin b → Fin (k + 1)) : ℝ) = ((k : ℝ) + 1) ^ b := by
          simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
            Nat.cast_one]
        have hfiber (z : ω ⊕ Fin (S * b) → Fin (k + 1)) (hz : z ∈ good) :
            1 / ((k : ℝ) + 1) ^ b ≤ ((fiber (transportWords e₁ R) z).dens : ℝ) := by
          rw [← hcard]
          refine one_div_card_le_dens ⟨pickSubspace hm hmb (B z) (fun _ ↦ 0), ?_⟩
          rw [mem_fiber, mem_transportWords]
          simpa only [htiledef, transportSubspace_apply] using htileR z hz (fun _ ↦ 0)
        rw [show (R.dens : ℝ) = 𝔼 z : (ω ⊕ Fin (S * b) → Fin (k + 1)),
            ((fiber (transportWords e₁ R) z).dens : ℝ) from ?_]
        · rw [show β / ((k : ℝ) + 1) ^ b = (1 / ((k : ℝ) + 1) ^ b) * β from by ring]
          refine le_trans (mul_le_mul_of_nonneg_left hgood (by positivity)) ?_
          rw [← Finset.expect_indicator_one (s := good), Finset.mul_expect]
          refine Finset.expect_le_expect fun z _ ↦ ?_
          by_cases hz : z ∈ good
          · rw [Set.indicator_of_mem (by simpa using hz)]
            simpa only [Pi.one_apply, mul_one] using hfiber z hz
          · rw [Set.indicator_of_notMem (by simpa using hz)]
            simp only [mul_zero]
            positivity
        · rw [average_density_fiber, dens_transportWords]
      -- the invariant survives for the remaining blocks
      have hins' : ∀ v : ω ⊕ Fin b → Fin (k + 1),
          IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e₂ (U \ R)) v) := by
        intro v
        rw [fiber_transportWords_sdiff]
        set u : ω → Fin (k + 1) := fun a ↦ v (Sum.inl a) with hu
        set x : Fin b → Fin (k + 1) := fun j ↦ v (Sum.inr j) with hx
        have hv : v = concat u x := (concat_inl_inr v).symm
        have hword (y : Fin (S * b) → Fin (k + 1)) :
            concat v y ∘ e₂ = concat (concat u y) x ∘ e₁ := by
          rw [hv, he₁, he₂]
          exact (concat_comp_swap e s u y x).symm
        have hUpart : IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e₂ U) v) := by
          rw [hv, he₂,
            fiber_transportWords_regroup e (s.trans (Equiv.sumComm (Fin (S * b)) (Fin b))) U u x]
          exact fiberSection (reindex _ (hins _)) _
        refine sdiff hUpart fun y y' hyy' ↦ ?_
        have hsection : B (concat u y) = B (concat u y') := by
          rw [hB, hB]
          exact fiber_congr (reindex s (hins u)) hyy'
        have hmemU : concat v y ∘ e₂ ∈ U ↔ concat v y' ∘ e₂ ∈ U := by
          have := hUpart (x := y) (y := y') hyy'
          rwa [mem_fiber, mem_transportWords, mem_fiber, mem_transportWords] at this
        have hout (z : Fin (S * b) → Fin (k + 1)) :
            (fun a ↦ (concat v z ∘ e₂) (e₁.symm (Sum.inl a))) = concat u z := by
          rw [hword z]
          funext a
          simp only [Function.comp_apply, Equiv.apply_symm_apply, concat_apply_inl]
        have hblock (z : Fin (S * b) → Fin (k + 1)) :
            (fun j ↦ (concat v z ∘ e₂) (e₁.symm (Sum.inr j))) = x := by
          rw [hword z]
          funext j
          simp only [Function.comp_apply, Equiv.apply_symm_apply, concat_apply_inr]
        have hmemR (z : Fin (S * b) → Fin (k + 1)) :
            z ∈ fiber (transportWords e₂ R) v ↔
              concat v z ∘ e₂ ∈ U ∧ concat u z ∈ good ∧
                x ∈ Subspace.range (pickSubspace hm hmb (B (concat u z))) := by
          rw [mem_fiber, mem_transportWords, hRdef, Finset.mem_filter, hout z, hblock z]
        rw [hmemR y, hmemR y']
        simp only [hgooddef, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hsection, hmemU]
      obtain ⟨𝒲, hfin', hcont', hdisj', hdens'⟩ := ih ι (ω ⊕ Fin b) e₂ (U \ R) hins'
      refine ⟨(tile '' (good : Set (ω ⊕ Fin (S * b) → Fin (k + 1)))) ∪ 𝒲, ?_, ?_, ?_, ?_⟩
      · exact (good.finite_toSet.image tile).union hfin'
      · intro V hV
        rcases hV with ⟨z, hz, rfl⟩ | hV
        · exact fun x ↦ hRU (htileR z hz x)
        · exact fun x ↦ (Finset.mem_sdiff.mp (hcont' V hV x)).1
      · refine Set.PairwiseDisjoint.union ?_ hdisj' ?_
        · rw [Set.pairwiseDisjoint_iff]
          intro V hV V' hV' hmeet
          obtain ⟨z, hz, rfl⟩ := hV
          obtain ⟨z', hz', rfl⟩ := hV'
          obtain ⟨w, hw, hw'⟩ := hmeet
          obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
          obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
          have hzz : z = z' := by
            funext a
            have h := congrFun (hx.trans hx'.symm) (e₁.symm (Sum.inl a))
            simpa only [htiledef, transportSubspace_apply, Function.comp_apply,
              Equiv.apply_symm_apply, concat_apply_inl] using h
          rw [hzz]
        · intro V hV V' hV' _
          obtain ⟨z, hz, rfl⟩ := hV
          rw [Set.disjoint_left]
          intro w hw hw'
          obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
          obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
          exact (Finset.mem_sdiff.mp (hx' ▸ hcont' V' hV' x')).2 (hx ▸ htileR z hz x)
      · have huncovered :
            uncovered U ((tile '' (good : Set (ω ⊕ Fin (S * b) → Fin (k + 1)))) ∪ 𝒲) =
              uncovered (U \ R) 𝒲 := by
          ext w
          simp only [uncovered, Finset.mem_filter, Finset.mem_sdiff, Set.mem_union, Set.mem_image]
          constructor
          · rintro ⟨hwU, hfree⟩
            refine ⟨⟨hwU, fun hwR ↦ ?_⟩, fun V hV ↦ hfree V (Or.inr hV)⟩
            obtain ⟨z, hz, hmem⟩ := hRtile w hwR
            exact hfree (tile z) (Or.inl ⟨z, hz, rfl⟩) hmem
          · rintro ⟨⟨hwU, hwR⟩, hfree⟩
            refine ⟨hwU, ?_⟩
            rintro V (⟨z, hz, rfl⟩ | hV)
            · intro hmem
              obtain ⟨x, hx⟩ := Subspace.mem_range.mp hmem
              exact hwR (hx ▸ htileR z hz x)
            · exact hfree V hV
        rw [huncovered]
        rcases hdens' with hlt | hle
        · exact Or.inl hlt
        · refine Or.inr ?_
          rw [dens_sdiff_of_subset hRU] at hle
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          linarith

/-- Finite-stage block packing gives one exact sufficient dimension for one-family tiling. -/
lemma exists_tilingSufficient_dimension (k m : ℕ) (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (_hβ₁ : β ≤ 1) :
    ∃ N, TilingSufficient k m β N := by
  by_cases hβ : β < 1
  · set b := max m (Subspace.restrictAlphabetBound k m β) with hbdef
    have hc : 0 < β / ((k : ℝ) + 1) ^ b := by positivity
    obtain ⟨T, hT⟩ := exists_nat_gt (1 / (β / ((k : ℝ) + 1) ^ b))
    rw [div_lt_iff₀ hc] at hT
    refine ⟨T * b, fun i D hD hDβ ↦ ?_⟩
    have hsections : ∀ v : Fin 0 → Fin (k + 1),
        IsInsensitive i.castSucc (Fin.last k)
          (fiber (transportWords (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D) v) := by
      intro v x y hxy
      simp only [mem_fiber, mem_transportWords]
      refine hD fun a hai hal c ↦ ?_
      simpa only [Function.comp_apply, Equiv.emptySum_symm_apply, concat_apply_inr] using
        hxy a hai hal c
    obtain ⟨𝒱, hfinite, hcontained, hpairwise, hconclusion⟩ :=
      exists_tiling_of_insensitive_sections i hDHJ hm (le_max_left _ _) hβ₀ hβ
        (le_max_right _ _) T (Fin (T * b)) (Fin 0)
        (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D hsections
    refine ⟨𝒱, hfinite, hcontained, hpairwise, ?_⟩
    rcases hconclusion with hlt | hle
    · exact hlt
    · exfalso
      have hD₁ : (D.dens : ℝ) ≤ 1 := by exact_mod_cast Finset.dens_le_one (s := D)
      have hnonneg : (0 : ℝ) ≤ ((uncovered D 𝒱).dens : ℝ) := by positivity
      linarith
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
lemma exists_eventually_tilingSufficient (k m : ℕ) (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, ∀ n ≥ N, TilingSufficient k m β n := by
  obtain ⟨N, hN⟩ := exists_tilingSufficient_dimension k m hDHJ hm hβ₀ hβ₁
  exact ⟨N, fun _n hn ↦ tilingSufficient_mono hN hn⟩

/-- A sufficient ambient dimension for tiling one insensitive family.  The tiling argument needs
density Hales--Jewett for the smaller alphabet, so the witness is selected under
`HasDensityHJ k`. -/
noncomputable def tilingBound (k m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : HasDensityHJ k ∧ 1 ≤ m ∧ 0 < β ∧ β ≤ 1 then
    Nat.find (exists_eventually_tilingSufficient k m h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 0

/-- The selected one-family tiling bound satisfies the tiling predicate in every larger
dimension. -/
lemma tilingBound_spec (k m n : ℕ) (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : tilingBound k m β ≤ n) : TilingSufficient k m β n := by
  classical
  rw [tilingBound, dif_pos ⟨hDHJ, hm, hβ₀, hβ₁⟩] at hn
  exact Nat.find_spec (exists_eventually_tilingSufficient k m hDHJ hm hβ₀ hβ₁) n hn

/-- A dense insensitive family can be tiled, up to small error, by disjoint subspaces. -/
lemma exists_disjoint_subspaces {k : ℕ} (i : Fin k) (hDHJ : HasDensityHJ k)
    (m n : ℕ) (hm : 1 ≤ m) (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : tilingBound k m β ≤ n) (D : Finset (Fin n → Fin (k + 1)))
    (hD : IsInsensitive i.castSucc (Fin.last k) D)
    (hDβ : 2 * β ≤ (D.dens : ℝ)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V D) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered D 𝒱).dens : ℝ) < 2 * β := by
  exact tilingBound_spec k m n hDHJ hm hβ₀ hβ₁ hn i D hD hDβ

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

/-- Mapping a parameter-cube family into a subspace scales its ambient density by the density of
the whole subspace range. -/
private lemma dens_map_subspace_eq_mul_range {α η ι : Type*}
    [Fintype (η → α)] [Fintype (ι → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (η → α)) :
    ((A.map ⟨V, Subspace.injective V⟩).dens : ℝ) =
      (A.dens : ℝ) * ((Subspace.range V).dens : ℝ) := by
  simp only [Finset.nnratCast_dens, Subspace.range, Finset.card_map]
  rw [Finset.card_image_iff.mpr (Subspace.injective V).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · letI : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hA : A = ∅ := Subsingleton.elim _ _
    rw [hA]
    simp
  · field_simp
    simp only [Finset.card_univ]

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
  let tiles := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    Classical.choose (existsInner V)
  have htiles (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      (tiles V).Finite ∧
      (∀ W ∈ tiles V, Subspace.IsContained W (pullback V)) ∧
      ((tiles V).PairwiseDisjoint fun W ↦
        (Subspace.range W : Set (Fin M → Fin (k + 1)))) ∧
      ((uncovered (pullback V) (tiles V)).dens : ℝ) < 2 * β :=
    Classical.choose_spec (existsInner V)
  let composed := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    Subspace.compose V '' tiles V
  have hcomposed (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      (composed V).Finite ∧
      (∀ U ∈ composed V, Subspace.IsContained U DLast) ∧
      ((composed V).PairwiseDisjoint fun U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
    exact composed_inner_tiles_facts DLast V (tiles V)
      (htiles V).1 (htiles V).2.1 (htiles V).2.2.1
  letI : Finite 𝒱 := hfinite
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ V : 𝒱, composed V
  refine ⟨global, ?_, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun V ↦ (hcomposed V).1
  · intro U hU x
    simp only [global, Set.mem_iUnion] at hU
    obtain ⟨V, hU⟩ := hU
    obtain ⟨W, hW, rfl⟩ := hU
    rw [mem_intersection]
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact (hcomposed V).2.1 (Subspace.compose V W)
        (by simpa only [composed] using
          Set.mem_image_of_mem (Subspace.compose V.val) hW) x
    · have hx := hcontained V V.prop (W x)
      rw [mem_intersection] at hx
      simpa only [Subspace.compose_apply, D₀] using hx j
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    simp only [global, Set.mem_iUnion] at hU hU'
    obtain ⟨V, hU⟩ := hU
    obtain ⟨V', hU'⟩ := hU'
    have hVV : V = V' := by
      apply Subtype.ext
      apply Set.pairwiseDisjoint_iff.mp hpairwise V.prop V'.prop
      obtain ⟨w, hw, hw'⟩ := hcommon
      obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
      obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
      obtain ⟨W, hW, rfl⟩ := hU
      obtain ⟨W', hW', rfl⟩ := hU'
      refine ⟨V.val (W x), Subspace.mem_range.mpr ⟨W x, rfl⟩,
        Subspace.mem_range.mpr ⟨W' x', ?_⟩⟩
      simpa only [Subspace.compose_apply] using hx'.trans hx.symm
    subst V'
    exact Set.pairwiseDisjoint_iff.mp (hcomposed V).2.2 hU hU' hcommon
  · let outer := hfinite.toFinset
    let innerError := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
      (uncovered (pullback V) (tiles V)).map ⟨V, Subspace.injective V⟩
    let errors := outer.biUnion innerError
    have herror_pairwise : (outer : Set _).PairwiseDisjoint innerError := by
      intro V hV V' hV' hVV
      change Disjoint (innerError V) (innerError V')
      rw [Finset.disjoint_left]
      intro w hw hw'
      apply Set.disjoint_left.mp (hpairwise
        (by simpa [outer] using hV)
        (by simpa [outer] using hV') hVV)
      · obtain ⟨x, _hx, hxw⟩ := Finset.mem_map.mp hw
        exact Subspace.mem_range.mpr ⟨x, hxw⟩
      · obtain ⟨x', _hx', hx'w⟩ := Finset.mem_map.mp hw'
        exact Subspace.mem_range.mpr ⟨x', hx'w⟩
    have herrors : (errors.dens : ℝ) ≤ 2 * β := by
      simp only [errors]
      rw [Finset.dens_biUnion herror_pairwise]
      change (NNRat.castHom ℝ) (∑ V ∈ outer, (innerError V).dens) ≤ 2 * β
      rw [map_sum (NNRat.castHom ℝ)]
      refine (Finset.sum_le_sum fun V hV ↦
        show ((innerError V).dens : ℝ) ≤
          2 * β * ((Subspace.range V).dens : ℝ) by
          dsimp only [innerError]
          rw [dens_map_subspace_eq_mul_range]
          apply mul_le_mul_of_nonneg_right (htiles V).2.2.2.le
          positivity).trans ?_
      rw [← Finset.mul_sum]
      have hranges_pairwise :
          (outer : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n))).PairwiseDisjoint
            (fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
              Subspace.range V) := by
        intro V hV V' hV' hVV
        change Disjoint (Subspace.range V) (Subspace.range V')
        rw [Finset.disjoint_left]
        intro w hw hw'
        apply Set.disjoint_left.mp (hpairwise
          (by simpa [outer] using hV)
          (by simpa [outer] using hV') hVV)
        · exact hw
        · exact hw'
      have hsum : (∑ V ∈ outer, ((Subspace.range V).dens : ℝ)) ≤ 1 := by
        have hdens_ranges :
            (((outer.biUnion Subspace.range).dens : ℚ≥0) : ℝ) =
              ∑ V ∈ outer, ((Subspace.range V).dens : ℝ) := by
          rw [Finset.dens_biUnion hranges_pairwise]
          change (NNRat.castHom ℝ)
            (∑ V ∈ outer, (Subspace.range V).dens) = _
          rw [map_sum (NNRat.castHom ℝ)]
          rfl
        rw [← hdens_ranges]
        exact_mod_cast Finset.dens_le_one (s := outer.biUnion Subspace.range)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hβ₀.le)
    have huncovered_subset :
        uncovered (intersection D) global ⊆
          uncovered (intersection D₀) 𝒱 ∪ errors := by
      intro w hw
      simp only [uncovered, Finset.mem_filter] at hw
      simp only [uncovered, Finset.mem_filter, Finset.mem_union]
      by_cases hparent : ∃ V ∈ 𝒱, w ∈ Subspace.range V
      · right
        obtain ⟨V, hV, hwV⟩ := hparent
        obtain ⟨x, hx⟩ := Subspace.mem_range.mp hwV
        refine Finset.mem_biUnion.mpr ⟨V, ?_, ?_⟩
        · simpa [outer] using hV
        · apply Finset.mem_map.mpr
          refine ⟨x, ?_, hx⟩
          simp only [uncovered, Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · simp only [pullback, parameterPreimage, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact hx ▸ (mem_intersection.mp hw.1 (Fin.last r))
          · intro W hW hxW
            apply hw.2 (Subspace.compose V W)
            · exact Set.mem_iUnion_of_mem ⟨V, hV⟩ <|
                Set.mem_image_of_mem (Subspace.compose V) hW
            · obtain ⟨y, hy⟩ := Subspace.mem_range.mp hxW
              exact Subspace.mem_range.mpr ⟨y, by
                rw [Subspace.compose_apply, hy, hx]⟩
      · left
        refine ⟨hsubset hw.1, ?_⟩
        intro V hV hwV
        exact hparent ⟨V, hV, hwV⟩
    have hdens :
        ((uncovered (intersection D) global).dens : ℝ) ≤
          ((uncovered (intersection D₀) 𝒱 ∪ errors).dens : ℝ) := by
      exact_mod_cast Finset.dens_mono huncovered_subset
    have hdens_union :
        ((uncovered (intersection D₀) 𝒱 ∪ errors).dens : ℝ) ≤
          ((uncovered (intersection D₀) 𝒱).dens : ℝ) + (errors.dens : ℝ) := by
      exact_mod_cast Finset.dens_union_le (uncovered (intersection D₀) 𝒱) errors
    refine hdens.trans_lt (lt_of_le_of_lt hdens_union ?_)
    convert add_lt_add_of_lt_of_le huncovered herrors using 1
    push_cast
    ring

/-- Induction on the number of insensitive families gives one exact sufficient intersection-tiling
dimension. -/
lemma exists_intersectionTilingSufficient_dimension (k r m : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, IntersectionTilingSufficient k r m β N := by
  induction r using Nat.strong_induction_on generalizing m with
  | h r ih =>
      obtain rfl | hr := r
      · omega
      obtain rfl | s := hr
      · obtain ⟨N, hN⟩ := exists_tilingSufficient_dimension k m hDHJ hm hβ₀ hβ₁
        exact ⟨N, intersectionTilingSufficient_one hN⟩
      · let M := max 1 (tilingBound k m β)
        have hM : 1 ≤ M := le_max_left _ _
        obtain ⟨N, houter⟩ :=
          ih (s + 1) (by omega) M (by omega) (by omega) hM
        have hinner : TilingSufficient k m β M :=
          tilingBound_spec k m M hDHJ hm hβ₀ hβ₁ (le_max_right _ _)
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
lemma exists_eventually_intersectionTilingSufficient (k r m : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    ∃ N, ∀ n ≥ N, IntersectionTilingSufficient k r m β n := by
  obtain ⟨N, hN⟩ :=
    exists_intersectionTilingSufficient_dimension k r m hDHJ hr₀ hrk hm hβ₀ hβ₁
  exact ⟨N, fun _n hn ↦ intersectionTilingSufficient_mono hN hn⟩

/-- A sufficient ambient dimension for tiling an intersection of insensitive families, again
selected under `HasDensityHJ k`. -/
noncomputable def intersectionTilingBound (k r m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : HasDensityHJ k ∧ 1 ≤ r ∧ r ≤ k ∧ 1 ≤ m ∧ 0 < β ∧ β ≤ 1 then
    Nat.find (exists_eventually_intersectionTilingSufficient
      k r m h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else 0

/-- The selected intersection-tiling bound satisfies the tiling predicate in every larger
dimension. -/
lemma intersectionTilingBound_spec (k r m n : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hn : intersectionTilingBound k r m β ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  classical
  rw [intersectionTilingBound,
    dif_pos ⟨hDHJ, hr₀, hrk, hm, hβ₀, hβ₁⟩] at hn
  exact Nat.find_spec
    (exists_eventually_intersectionTilingSufficient k r m hDHJ hr₀ hrk hm hβ₀ hβ₁) n hn

/-- An intersection of insensitive families can be tiled by disjoint subspaces. -/
lemma exists_disjoint_subspaces_iInter {k : ℕ} (r m n : ℕ) (hDHJ : HasDensityHJ k)
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
  exact intersectionTilingBound_spec k r m n hDHJ hr₀ hrk hm hβ₀ hβ₁ hn
    hr₀ hrk D hD hDβ

end IsInsensitive
end DensityHalesJewett

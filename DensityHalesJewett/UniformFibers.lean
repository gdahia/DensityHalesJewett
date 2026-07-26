/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.GrahamRothschild
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Linarith

/-!
# Preliminary density lemmas

Multidimensional density Hales--Jewett, uniform fibers, and the restricted-alphabet subspace
lemma.  All subspaces below are mathlib's `Combinatorics.Subspace`.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- The density Hales--Jewett assertion for the alphabet `Fin k`. -/
def HasDensityHJ (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ #A → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A

namespace Subspace

/-- A one-dimensional density Hales--Jewett threshold selected from `HasDensityHJ`. -/
noncomputable def densityOneBound (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.find (h.2 δ h.1)
  else 0

lemma densityOneBound_spec {k : ℕ} (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityOneBound k δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A := by
  classical
  rw [densityOneBound, dif_pos ⟨hδ, hDHJ⟩] at hn
  exact Nat.find_spec (hDHJ δ hδ) n hn A hA

/-- The one-dimensional case of multidimensional density Hales--Jewett. -/
lemma exists_one_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : densityOneBound k δ ≤ n)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin 1) (Fin k) (Fin n), IsContained V A := by
  obtain ⟨l, hl⟩ := densityOneBound_spec hDHJ δ hδ n hn A hA
  refine ⟨lineToSubspaceFinOne l, ?_⟩
  intro x
  rw [lineToSubspaceFinOne_apply]
  exact hl _

/-- The number of line structures in a finite cube is bounded by the number of index words. -/
lemma card_line_le (k m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))] :
    Fintype.card (Combinatorics.Line (Fin k) (Fin m)) ≤ (k + 1) ^ m := by
  classical
  refine (Fintype.card_le_of_injective (fun l ↦ l.idxFun) fun l₁ l₂ h ↦ ?_).trans ?_
  · cases l₁
    cases l₂
    cases h
    rfl
  · simp

/-- A line is equivalently an `Option`-valued index word with at least one variable
coordinate. -/
private noncomputable def lineIndexEquiv (α ι : Type*) :
    Combinatorics.Line α ι ≃
      {f : ι → Option α // ¬ ∀ i, f i ≠ none} := by
  classical
  refine {
    toFun := fun l ↦ ⟨l.idxFun, fun h ↦ ?_⟩
    invFun := fun f ↦ {
      idxFun := f
      proper := by
        have hf := f.property
        push Not at hf
        exact hf
    }
    left_inv := ?_
    right_inv := ?_
  }
  · obtain ⟨i, hi⟩ := l.proper
    exact h i hi
  · intro l
    cases l
    rfl
  · intro f
    apply Subtype.ext
    rfl

/-- An index word with no variable coordinate is equivalently an ordinary alphabet word. -/
private noncomputable def fixedIndexWordEquiv (α ι : Type*) [Nonempty α] :
    {f : ι → Option α // ∀ i, f i ≠ none} ≃ (ι → α) := by
  classical
  let a : α := Classical.choice inferInstance
  refine {
    toFun := fun f i ↦ (f.1 i).getD a
    invFun := fun x ↦ ⟨some ∘ x, by
      intro i
      change some (x i) ≠ none
      exact Option.some_ne_none (x i)⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro f
    apply Subtype.ext
    funext i
    cases hi : f.1 i with
    | none => exact (f.2 i hi).elim
    | some b =>
        simp only [Function.comp_apply]
        rw [hi]
        rfl
  · intro x
    funext i
    simp only [Function.comp_apply, Option.getD_some]

/-- The exact number of combinatorial line structures in a nonempty finite-alphabet word cube. -/
lemma card_line (k m : ℕ) (hk : 0 < k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] :
    Fintype.card (Combinatorics.Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [Fintype.card_congr (lineIndexEquiv (Fin k) (Fin m)),
    Fintype.card_subtype_compl (fun f : Fin m → Option (Fin k) ↦ ∀ i, f i ≠ none),
    Fintype.card_pi_const, Fintype.card_option, Fintype.card_fin,
    Fintype.card_congr (fixedIndexWordEquiv (Fin k) (Fin m)),
    Fintype.card_pi_const, Fintype.card_fin]

/-- The finite enumeration of line structures induced by their index words. -/
@[instance_reducible]
noncomputable def lineFintype (k m : ℕ) : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
  Fintype.ofInjective (fun l ↦ l.idxFun) fun l₁ l₂ h ↦ by
    cases l₁
    cases l₂
    cases h
    rfl

/-- A subspace over the empty alphabet, obtained by repeating parameter coordinates. -/
def emptyAlphabetSubspace {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Combinatorics.Subspace (Fin m) (Fin 0) (Fin n) where
  idxFun i := Sum.inr ⟨i.val % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm)⟩
  proper e := by
    refine ⟨Fin.castLE hmn e, ?_⟩
    simp only [Sum.inr.injEq]
    apply Fin.ext
    exact Nat.mod_eq_of_lt e.isLt

/-- Every empty-alphabet subspace is contained in every word family. -/
lemma emptyAlphabetSubspace_isContained {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Finset (Fin n → Fin 0)) : IsContained (emptyAlphabetSubspace hm hmn) A := by
  intro x
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)

/-- Convert the cardinal density hypothesis to the normalized finite-set density inequality. -/
lemma density_le_of_card_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    δ ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  refine (le_div_iff₀ ?_).mpr ?_
  · simp only [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  · simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using hA

/-- Convert a normalized density lower bound back to the cardinal form used by the
density Hales--Jewett assertion. -/
lemma card_le_of_density_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ * (k : ℝ) ^ n ≤ #A := by
  rw [Finset.nnratCast_dens] at hA
  have hpos : 0 < (Fintype.card (Fin n → Fin k) : ℝ) := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  have hcard := (le_div_iff₀ hpos).mp hA
  simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using hcard

/-- One fiber of a map to a finite nonempty type has at least the average relative density. -/
lemma exists_fiber_density {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (s : Finset X) (f : X → Y) :
    ∃ y, (s.filter fun x ↦ f x = y).dens ≥ (s.dens : ℝ) / Fintype.card Y := by
  classical
  let b : ℝ := #s / Fintype.card Y
  have hb : (#(Finset.univ : Finset Y) : ℕ) • b ≤ ∑ _x ∈ s, (1 : ℝ) := by
    simp only [Finset.card_univ, nsmul_eq_mul, b]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨y, _, hy⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (s := s) (t := Finset.univ)
      (f := f) (w := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ Finset.mem_univ _)
      Finset.univ_nonempty hb
  refine ⟨y, ?_⟩
  rw [Finset.nnratCast_dens, Finset.nnratCast_dens]
  change (#s : ℝ) / Fintype.card Y ≤ ∑ x ∈ s with f x = y, (1 : ℝ) at hy
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hy
  rw [ge_iff_le]
  simpa only [div_div, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_one] using
    div_le_div_of_nonneg_right hy (by positivity : 0 ≤ (Fintype.card X : ℝ))

/-- At least half the ambient density lies on prefixes with fiber density at least half as large. -/
lemma half_density_prefixes {k p q : ℕ} (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ / 2 ≤
      ((Finset.univ.filter fun x : Fin p → Fin k ↦ δ / 2 ≤ ((fiber A x).dens : ℝ)).dens : ℝ) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Nonempty (Fin p → Fin k) := Pi.instNonempty
  have hδ₁ : δ ≤ 1 := hA.trans (by exact_mod_cast Finset.dens_le_one (s := A))
  have hthreshold := density_ge_threshold (fun x : Fin p → Fin k ↦ ((fiber A x).dens : ℝ))
    δ (δ / 2) (fun _ ↦ by positivity)
    (fun x ↦ by exact_mod_cast Finset.dens_le_one (s := fiber A x))
    (by linarith)
    (by linarith) (by simpa only [average_density_fiber] using hA)
  refine le_trans ?_ hthreshold
  refine (le_div_iff₀ ?_).mpr ?_
  · linarith
  · nlinarith

/-- A dense suffix fiber contains a line whose points remain in the ambient family. -/
lemma exists_line_of_fiber_density {k p q : ℕ} (hk : 0 < k) (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : densityOneBound k δ ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (x : Fin p → Fin k)
    (hx : δ ≤ ((fiber A x).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q), ∀ a, DensityHalesJewett.concat x (l a) ∈ A := by
  obtain ⟨l, hl⟩ :=
    densityOneBound_spec hDHJ δ hδ q hq (fiber A x)
      (card_le_of_density_le hk δ (fiber A x) hx)
  refine ⟨l, ?_⟩
  intro a
  exact mem_fiber.mp (hl a)

/-- One suffix line is complete above a positive-density family of prefixes. -/
lemma exists_common_dense_line {k p q : ℕ} (hk : 0 < k) (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : densityOneBound k (δ / 2) ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    letI := lineFintype k q
    ∃ l : Combinatorics.Line (Fin k) (Fin q),
      δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q))) ≤
        ((Finset.univ.filter fun x : Fin p → Fin k ↦
          ∀ a, DensityHalesJewett.concat x (l a) ∈ A).dens : ℝ) := by
  classical
  letI := lineFintype k q
  let B := Finset.univ.filter fun x : Fin p → Fin k ↦
    δ / 2 ≤ ((fiber A x).dens : ℝ)
  have hB : δ / 2 ≤ (B.dens : ℝ) := half_density_prefixes hk δ hδ A hA
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.dens_empty] at hB
    norm_num at hB
    linarith
  let x₀ := hBne.choose
  have hx₀ : x₀ ∈ B := hBne.choose_spec
  obtain ⟨l₀, _⟩ := exists_line_of_fiber_density hk hDHJ (δ / 2) (by linarith) hq A x₀
    (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hx₀)
  letI : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let lineAt : {x // x ∈ B} → Combinatorics.Line (Fin k) (Fin q) := fun x ↦
    Classical.choose <| exists_line_of_fiber_density hk hDHJ (δ / 2) (by linarith)
      hq A x (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using x.2)
  let f : (Fin p → Fin k) → Combinatorics.Line (Fin k) (Fin q) := fun x ↦
    if hx : x ∈ B then lineAt ⟨x, hx⟩ else l₀
  obtain ⟨l, hl⟩ := exists_fiber_density B f
  refine ⟨l, le_trans ?_ (le_trans hl ?_)⟩
  · simpa only [div_div] using
      div_le_div_of_nonneg_right hB
        (by positivity : 0 ≤ (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ))
  · exact_mod_cast Finset.dens_le_dens <| by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hfl : lineAt ⟨x, hx.1⟩ = l := by
        simpa only [f, dif_pos hx.1] using hx.2
      intro a
      rw [← hfl]
      exact Classical.choose_spec
        (exists_line_of_fiber_density hk hDHJ (δ / 2) (by linarith) hq A x
          (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hx.1)) a

/-- Every positive target density eventually forces a subspace of any fixed positive
dimension. -/
lemma exists_eventually_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n hmn A _
    exact ⟨emptyAlphabetSubspace hm hmn, emptyAlphabetSubspace_isContained hm hmn A⟩
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  induction m, hm using Nat.le_induction generalizing δ with
  | base =>
      exact ⟨densityOneBound k δ, fun n hn A hA ↦
        exists_one_of_density hDHJ δ hδ n hn A hA⟩
  | succ m hm ih =>
      let q := max 1 (densityOneBound k (δ / 2))
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      have hq : densityOneBound k (δ / 2) ≤ q := le_max_right _ _
      letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
      letI := lineFintype k q
      let ε := δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q)))
      have hε : 0 < ε := by
        have hlinecard : 0 < Fintype.card (Combinatorics.Line (Fin k) (Fin q)) :=
          Fintype.card_pos
        dsimp only [ε]
        exact div_pos hδ (by exact_mod_cast mul_pos (by norm_num : 0 < (2 : ℕ)) hlinecard)
      obtain ⟨P, hP⟩ := ih ε hε
      refine ⟨P + q, ?_⟩
      intro n hn A hA
      let p := n - q
      have hqn : q ≤ n := by omega
      have hpq : p + q = n := Nat.sub_add_cancel hqn
      have hPp : P ≤ p := by omega
      let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
      let wordEquiv : (Fin p ⊕ Fin q → Fin k) ≃ (Fin n → Fin k) :=
        e.arrowCongr (Equiv.refl _)
      let A' := A.map wordEquiv.symm.toEmbedding
      have hA' : δ ≤ (A'.dens : ℝ) := by
        simpa only [A', Finset.dens_map_equiv] using density_le_of_card_le hk δ A hA
      obtain ⟨l, hl⟩ := exists_common_dense_line hk hDHJ δ hδ hq A' hA'
      let C := Finset.univ.filter fun x : Fin p → Fin k ↦
        ∀ a, DensityHalesJewett.concat x (l a) ∈ A'
      have hC : ε ≤ (C.dens : ℝ) := by
        simpa only [ε, C] using hl
      obtain ⟨V, hV⟩ := hP p hPp C (card_le_of_density_le hk ε C hC)
      let W₀ : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin p ⊕ Fin q) :=
        (Subspace.concat V (lineToSubspaceFinOne l)).reindex finSumFinEquiv
          (Equiv.refl _) (Equiv.refl _)
      let W : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin n) :=
        W₀.reindex (Equiv.refl _) (Equiv.refl _) e
      refine ⟨W, ?_⟩
      intro z
      let x : Fin m → Fin k := fun i ↦ z (finSumFinEquiv (Sum.inl i))
      let a : Fin k := z (finSumFinEquiv (Sum.inr 0))
      have hx : DensityHalesJewett.concat (V x) (l a) ∈ A' := by
        have hxC : ∀ b, DensityHalesJewett.concat (V x) (l b) ∈ A' := by
          simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hV x
        exact hxC a
      rw [Finset.mem_map_equiv] at hx
      simp only [Equiv.symm_symm] at hx
      convert hx using 1
      funext i
      simp only [W, W₀, Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
        Equiv.refl_symm]
      change (Subspace.concat V (lineToSubspaceFinOne l)) (z ∘ finSumFinEquiv) (e.symm i) =
        wordEquiv (DensityHalesJewett.concat (V x) (l a)) i
      have hz : z ∘ finSumFinEquiv =
          DensityHalesJewett.concat x (fun _ : Fin 1 ↦ a) := by
        funext j
        cases j with
        | inl j => rfl
        | inr j => exact congrArg z (congrArg finSumFinEquiv (congrArg Sum.inr (Fin.eq_zero j)))
      rw [hz, Subspace.concat_apply, lineToSubspaceFinOne_apply]
      rfl

/-- A bound for multidimensional density Hales--Jewett. -/
noncomputable def densityBound (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ HasDensityHJ k then
    Nat.find (exists_eventually_of_density h.2.2 m h.1 δ h.2.1)
  else 0

lemma densityBound_spec {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  rw [densityBound, dif_pos ⟨hm, hδ, hDHJ⟩] at hn
  exact Nat.find_spec (exists_eventually_of_density hDHJ m hm δ hδ) n hn A hA

/-- Multidimensional density Hales--Jewett follows from the one-dimensional assertion. -/
lemma exists_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  exact densityBound_spec hDHJ m hm δ hδ n hn A hA

/-- Split the coordinates of a word family into a prefix and a suffix along a cut equivalence. -/
def splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : Finset (Fin p ⊕ Fin q → Fin alphabet) :=
  A.map (e.arrowCongr (Equiv.refl (Fin alphabet))).symm.toEmbedding

@[simp]
lemma mem_splitWords {alphabet p q n : ℕ} {e : Fin p ⊕ Fin q ≃ Fin n}
    {A : Finset (Fin n → Fin alphabet)} {w : Fin p ⊕ Fin q → Fin alphabet} :
    w ∈ splitWords e A ↔ w ∘ e.symm ∈ A := by
  rw [splitWords, Finset.mem_map_equiv, Equiv.symm_symm]
  rfl

@[simp]
lemma dens_splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : (splitWords e A).dens = A.dens := by
  rw [splitWords, Finset.dens_map_equiv]

/-- The canonical cut equivalence associated with a decomposition of the ambient dimension. -/
def cutEquiv {p q n : ℕ} (h : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

/-- The subspace of a coordinate block whose parameter directions are all of its coordinates. -/
def blockSubspace (α : Type*) (m : ℕ) : Combinatorics.Subspace (Fin m) α (Fin m) where
  idxFun i := Sum.inr i
  proper e := ⟨e, rfl⟩

@[simp]
lemma blockSubspace_apply {α : Type*} {m : ℕ} (x : Fin m → α) : blockSubspace α m x = x := by
  funext i
  exact (blockSubspace α m).apply_inr rfl

/-- Prepend a fixed block of letters to the coordinates of a subspace. -/
def prependFixed {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) : Combinatorics.Subspace η α (Fin (m + p)) where
  idxFun i :=
    match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (u j)
    | Sum.inr j => V.idxFun j
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨finSumFinEquiv (Sum.inr i), by simp only [Equiv.symm_apply_apply, hi]⟩

@[simp]
lemma prependFixed_apply {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) (x : η → α) :
    prependFixed u V x = DensityHalesJewett.concat u (V x) ∘ finSumFinEquiv.symm := by
  funext i
  simp only [Function.comp_apply, Combinatorics.Subspace.coe_apply, prependFixed]
  cases hi : finSumFinEquiv.symm i with
  | inl j => simp only [DensityHalesJewett.concat_apply_inl, Sum.elim_inl, id_eq]
  | inr j =>
      rw [DensityHalesJewett.concat_apply_inr, Combinatorics.Subspace.coe_apply]

/-- Regroup a cut of the coordinates following a fixed block. -/
def prependCoords {m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin m ⊕ Fin r :=
  ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin q))).trans
      (Equiv.sumAssoc (Fin m) (Fin p) (Fin q))).trans ((Equiv.refl (Fin m)).sumCongr e)

/-- Prepend a fixed coordinate block to a cut of the remaining coordinates. -/
def prependCut {m p q r n : ℕ} (h : m + r = n) (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin n :=
  (prependCoords e).trans (cutEquiv h)

/-- Regrouping the coordinates identifies a prepended word with the concatenation of the fixed
block and the cut word. -/
lemma concat_prependFixed {alphabet η m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r)
    (u : Fin m → Fin alphabet) (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    DensityHalesJewett.concat (prependFixed u V x) y ∘ (prependCoords e).symm =
      DensityHalesJewett.concat u (DensityHalesJewett.concat (V x) y ∘ e.symm) := by
  funext s
  cases s with
  | inl a => simp [prependCoords, DensityHalesJewett.concat]
  | inr b =>
      cases hb : e.symm b with
      | inl c => simp [prependCoords, DensityHalesJewett.concat, hb]
      | inr d => simp [prependCoords, DensityHalesJewett.concat, hb]

/-- The same identification stated for the cut of the ambient coordinates. -/
lemma concat_prependFixed_cut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    DensityHalesJewett.concat (prependFixed u V x) y ∘ (prependCut h e).symm =
      DensityHalesJewett.concat u (DensityHalesJewett.concat (V x) y ∘ e.symm) ∘
        (cutEquiv h).symm := by
  rw [← concat_prependFixed e u V x y]
  rfl

/-- The suffix fibers of a prepended cut are the suffix fibers of the family already restricted
to the fixed prefix block. -/
lemma fiber_splitWords_prependCut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (A : Finset (Fin n → Fin alphabet)) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p)) (x : Fin η → Fin alphabet) :
    fiber (splitWords (prependCut h e) A) (prependFixed u V x) =
      fiber (splitWords e (fiber (splitWords (cutEquiv h) A) u)) (V x) := by
  ext y
  simp only [mem_fiber, mem_splitWords]
  rw [concat_prependFixed_cut]

/-- A prefix fiber sparser than the ambient density by `ε` forces another prefix fiber denser
than the ambient density by a fixed amount. -/
lemma exists_denser_fiber {alphabet m q : ℕ} (halphabet : 0 < alphabet) {ε : ℝ} (hε : 0 < ε)
    (A : Finset (Fin m ⊕ Fin q → Fin alphabet)) (u₀ : Fin m → Fin alphabet)
    (hu₀ : ((fiber A u₀).dens : ℝ) < (A.dens : ℝ) - ε) :
    ∃ u, (A.dens : ℝ) + ε / (alphabet : ℝ) ^ m ≤ ((fiber A u).dens : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  have halphabetR : (0 : ℝ) < (alphabet : ℝ) := by exact_mod_cast halphabet
  have hcard : (Fintype.card (Fin m → Fin alphabet) : ℝ) = (alphabet : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hsum : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) =
      (alphabet : ℝ) ^ m * (A.dens : ℝ) := by
    rw [← average_density_fiber A, ← hcard, ← Finset.card_univ, Finset.card_mul_expect]
  have hle : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) ≤
      ∑ u : Fin m → Fin alphabet, (((A.dens : ℝ) + ε / (alphabet : ℝ) ^ m) +
        if u = u₀ then -(ε + ε / (alphabet : ℝ) ^ m) else 0) := by
    refine Finset.sum_le_sum fun u _ ↦ ?_
    by_cases hu : u = u₀
    · rw [hu, if_pos rfl]
      linarith
    · rw [if_neg hu, add_zero]
      linarith [hcon u]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ u₀,
    if_pos (Finset.mem_univ u₀), Finset.card_univ, nsmul_eq_mul, hcard, hsum, mul_add,
    mul_div_cancel₀ ε (by positivity : ((alphabet : ℝ) ^ m) ≠ 0)] at hle
  have hεpos : 0 < ε / (alphabet : ℝ) ^ m := by positivity
  linarith

/-- Every ambient dimension admits a cut into a prefix carrying a subspace and a nonempty suffix
above which all fibers are almost as dense as the whole family. -/
def VariableCutFibersSufficient (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin alphabet),
    ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ)

/-- The block density-increment argument: one coordinate block either uniformizes all suffix
fibers or increases the working density by a fixed amount, and the density upper bound bounds the
number of increments. -/
private lemma exists_variableCut_of_fuel (alphabet dimension : ℕ) (halphabet : 0 < alphabet)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t n : ℕ, dimension * (t + 1) < n → ∀ A : Finset (Fin n → Fin alphabet),
      1 ≤ (A.dens : ℝ) + t * (ε / (alphabet : ℝ) ^ dimension) →
      ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
        ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
          ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      intro n hn A hfuel
      have hblock : dimension ≤ dimension * (t + 1) :=
        Nat.le_mul_of_pos_right dimension (Nat.succ_pos t)
      have hd : dimension + (n - dimension) = n := by omega
      have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension := by
        have : (0 : ℝ) < (alphabet : ℝ) := by exact_mod_cast halphabet
        positivity
      by_cases hsucc :
          ∀ u, (A.dens : ℝ) - ε ≤ ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ)
      · exact ⟨dimension, n - dimension, cutEquiv hd, by omega,
          blockSubspace (Fin alphabet) dimension, by simpa only [blockSubspace_apply] using hsucc⟩
      push Not at hsucc
      obtain ⟨u₀, hu₀⟩ := hsucc
      obtain ⟨u, hu⟩ := exists_denser_fiber halphabet hε (splitWords (cutEquiv hd) A) u₀
        (by rwa [dens_splitWords])
      rw [dens_splitWords] at hu
      have hu₁ : ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ) ≤ 1 := by
        exact_mod_cast Finset.dens_le_one (s := fiber (splitWords (cutEquiv hd) A) u)
      have htR : (1 : ℝ) ≤ (t : ℝ) := by
        nlinarith [mul_pos hεpos hεpos]
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
        have : 1 ≤ t := by exact_mod_cast htR
        omega⟩
      have hstep : dimension * (s + 1 + 1) = dimension * (s + 1) + dimension := by ring
      obtain ⟨p, q, e, hq, V, hV⟩ := ih s (by omega) (n - dimension) (by omega)
        (fiber (splitWords (cutEquiv hd) A) u)
        (by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hfuel; linarith)
      refine ⟨dimension + p, q, prependCut hd e, hq, prependFixed u V, ?_⟩
      intro x
      rw [fiber_splitWords_prependCut]
      linarith [hV x]

/-- Every sufficiently large ambient dimension is sufficient for variable-cut uniform fibers. -/
lemma exists_eventually_variableCutFibersSufficient (alphabet dimension : ℕ)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, VariableCutFibersSufficient alphabet dimension ε n := by
  classical
  by_cases halphabet : alphabet = 0
  · subst alphabet
    refine ⟨dimension + 1, ?_⟩
    intro n hn A
    refine ⟨dimension, n - dimension, cutEquiv (by omega), by omega,
      emptyAlphabetSubspace hdimension le_rfl, ?_⟩
    intro x
    exact Fin.elim0 (x ⟨0, hdimension⟩)
  have halphabet₀ : 0 < alphabet := Nat.pos_of_ne_zero halphabet
  have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension := by
    have : (0 : ℝ) < (alphabet : ℝ) := by exact_mod_cast halphabet₀
    positivity
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / (ε / (alphabet : ℝ) ^ dimension))
  refine ⟨dimension * (t + 1) + 1, ?_⟩
  intro n hn A
  refine exists_variableCut_of_fuel alphabet dimension halphabet₀ hε t n (by omega) A ?_
  rw [div_lt_iff₀ hεpos] at ht
  have hdens : (0 : ℝ) ≤ (A.dens : ℝ) := by positivity
  linarith

/-- A sufficient ambient dimension for the variable-cut uniform-fibers lemma. -/
noncomputable def variableCutFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ dimension ∧ 0 < ε then
    Nat.find (exists_eventually_variableCutFibersSufficient alphabet dimension h.1 h.2)
  else 0

/-- The selected variable-cut bound is sufficient in every larger ambient dimension. -/
lemma variableCutFibersBound_spec (alphabet dimension n : ℕ) (hdimension : 1 ≤ dimension)
    {ε : ℝ} (hε : 0 < ε) (hn : variableCutFibersBound alphabet dimension ε ≤ n) :
    VariableCutFibersSufficient alphabet dimension ε n := by
  classical
  rw [variableCutFibersBound, dif_pos ⟨hdimension, hε⟩] at hn
  exact Nat.find_spec
    (exists_eventually_variableCutFibersSufficient alphabet dimension hdimension hε) n hn

/-- A finite prefix dimension is sufficient for uniform fibers over the finite cardinal models. -/
def UniformFibersFinSufficient (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ q : ℕ, ∀ A : Finset (Fin n ⊕ Fin q → Fin alphabet), ε < (A.dens : ℝ) →
    ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin n),
      ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A (V x)).dens : ℝ)

/-- Pad a finite-coordinate subspace by fixed final coordinates. -/
private def padPrefixSubspace {α η : Type*} {p r n : ℕ}
    (e : Fin p ⊕ Fin r ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin p)) :
    Combinatorics.Subspace η α (Fin n) where
  idxFun i :=
    match e.symm i with
    | Sum.inl j => V.idxFun j
    | Sum.inr j => Sum.inl (z j)
  proper a := by
    obtain ⟨i, hi⟩ := V.proper a
    refine ⟨e (Sum.inl i), ?_⟩
    simp only [Equiv.symm_apply_apply, hi]

@[simp]
private lemma padPrefixSubspace_apply {α η : Type*} {p r n : ℕ}
    (e : Fin p ⊕ Fin r ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin p)) (x : η → α) :
    padPrefixSubspace e z V x =
      DensityHalesJewett.concat (V x) z ∘ e.symm := by
  funext i
  cases hi : e.symm i with
  | inl j =>
      simp [padPrefixSubspace, Combinatorics.Subspace.coe_apply, hi,
        DensityHalesJewett.concat, Function.comp_apply]
  | inr j =>
      simp [padPrefixSubspace, Combinatorics.Subspace.coe_apply, hi,
        DensityHalesJewett.concat, Function.comp_apply]

/-- Density Hales--Jewett for the prefix alphabet supplies the uniform-fibers statement by
thresholding the prefix words according to their suffix-fiber densities. -/
private lemma exists_uniformFibersFinSufficient_of_densityHJ
    (alphabet dimension : ℕ) (hDHJ : HasDensityHJ alphabet)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ N, UniformFibersFinSufficient alphabet dimension ε N := by
  classical
  by_cases halphabet : alphabet = 0
  · subst alphabet
    refine ⟨dimension, ?_⟩
    intro q A hA
    have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w _
      exact Fin.elim0 (w (Sum.inl ⟨0, Nat.zero_lt_of_lt hdimension⟩))
    rw [hAempty, Finset.dens_empty] at hA
    norm_num at hA
    linarith
  have halphabet₀ : 0 < alphabet := Nat.pos_of_ne_zero halphabet
  letI : Nonempty (Fin alphabet) := ⟨⟨0, halphabet₀⟩⟩
  obtain ⟨N, hN⟩ :=
    exists_eventually_of_density hDHJ dimension hdimension ε hε₀
  letI : Nonempty (Fin N → Fin alphabet) := Pi.instNonempty
  refine ⟨N, ?_⟩
  intro q A hA
  let good := Finset.univ.filter fun x : Fin N → Fin alphabet ↦
    (A.dens : ℝ) - ε ≤ ((fiber A x).dens : ℝ)
  have hAdens : (A.dens : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one (s := A)
  have hgood :
      ε ≤ (good.dens : ℝ) := by
    have hthreshold := density_ge_threshold
      (fun x : Fin N → Fin alphabet ↦ ((fiber A x).dens : ℝ))
      (A.dens : ℝ) ((A.dens : ℝ) - ε)
      (fun _ ↦ by positivity)
      (fun x ↦ by exact_mod_cast Finset.dens_le_one (s := fiber A x))
      (by linarith) (by linarith)
      (by simpa only [average_density_fiber] using le_rfl)
    refine le_trans ?_ hthreshold
    have hdenominator : 0 < 1 - ((A.dens : ℝ) - ε) := by linarith
    rw [le_div_iff₀ hdenominator]
    nlinarith
  obtain ⟨V, hV⟩ :=
    hN N le_rfl good (card_le_of_density_le halphabet₀ ε good hgood)
  refine ⟨V, ?_⟩
  intro x
  simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hV x

/-- A sufficiently large prefix contains a subspace above all of whose points the suffix fibers
retain almost all of the ambient density. -/
lemma exists_uniformFibersFinSufficient (alphabet dimension : ℕ)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ N, UniformFibersFinSufficient alphabet dimension ε N := by
  sorry

/-- Sufficiency for uniform fibers is upward closed after padding with unused final coordinates. -/
lemma exists_eventually_uniformFibersFinSufficient (alphabet dimension : ℕ)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ N, ∀ n ≥ N, UniformFibersFinSufficient alphabet dimension ε n := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    exists_uniformFibersFinSufficient alphabet dimension hdimension hε₀ hε₁
  let N := max N₀ dimension
  refine ⟨N, ?_⟩
  intro n hn q A hA
  have hN₀n : N₀ ≤ n := (le_max_left N₀ dimension).trans hn
  by_cases halphabet : alphabet = 0
  · subst alphabet
    have hdimn : dimension ≤ n := (le_max_right N₀ dimension).trans hn
    have hn₀ : 0 < n := by omega
    have hA₀ : (A.dens : ℝ) = 0 := by
      have hAempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w _
        exact Fin.elim0 (w (Sum.inl ⟨0, hn₀⟩))
      rw [hAempty, Finset.dens_empty]
      norm_num
    rw [hA₀] at hA
    linarith
  have halphabet₀ : 0 < alphabet := Nat.pos_of_ne_zero halphabet
  let r := n - N₀
  have hNr : N₀ + r = n := Nat.add_sub_of_le hN₀n
  let e : Fin N₀ ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr hNr)
  let coord : Fin r ⊕ (Fin N₀ ⊕ Fin q) ≃ Fin n ⊕ Fin q := {
    toFun := fun s ↦
      match s with
      | Sum.inl j => Sum.inl (e (Sum.inr j))
      | Sum.inr (Sum.inl i) => Sum.inl (e (Sum.inl i))
      | Sum.inr (Sum.inr j) => Sum.inr j
    invFun := fun s ↦
      match s with
      | Sum.inl i =>
          match e.symm i with
          | Sum.inl j => Sum.inr (Sum.inl j)
          | Sum.inr j => Sum.inl j
      | Sum.inr j => Sum.inr (Sum.inr j)
    left_inv := by
      intro s
      rcases s with j | ⟨i | j⟩
      · simp only [Equiv.symm_apply_apply]
      · simp only [Equiv.symm_apply_apply]
      · rfl
    right_inv := by
      intro s
      rcases s with i | j
      · cases hi : e.symm i with
        | inl a =>
            have hei := congrArg e hi
            simp only [Equiv.apply_symm_apply] at hei
            subst i
            simp only [Equiv.symm_apply_apply]
        | inr a =>
            have hei := congrArg e hi
            simp only [Equiv.apply_symm_apply] at hei
            subst i
            simp only [Equiv.symm_apply_apply]
      · rfl
  }
  let wordEquiv := coord.arrowCongr (Equiv.refl (Fin alphabet))
  let A' := A.map wordEquiv.symm.toEmbedding
  have hA' : (A'.dens : ℝ) = (A.dens : ℝ) := by
    simp only [A', Finset.dens_map_equiv]
  have havg :
      (A.dens : ℝ) ≤
        𝔼 z : Fin r → Fin alphabet, ((fiber A' z).dens : ℝ) := by
    rw [average_density_fiber, hA']
  letI : Nonempty (Fin alphabet) := ⟨⟨0, halphabet₀⟩⟩
  letI : Nonempty (Fin r → Fin alphabet) := Pi.instNonempty
  obtain ⟨z, _, hz⟩ :=
    Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  let B := fiber A' z
  obtain ⟨V₀, hV₀⟩ := hN₀ q B (hA.trans_le hz)
  let V := padPrefixSubspace e z V₀
  refine ⟨V, ?_⟩
  intro x
  have hword (y : Fin q → Fin alphabet) :
      wordEquiv (DensityHalesJewett.concat z
        (DensityHalesJewett.concat (V₀ x) y)) =
          DensityHalesJewett.concat (V x) y := by
    funext i
    rcases i with i | j
    · cases hi : e.symm i with
      | inl a =>
          simp [wordEquiv, coord, V, Equiv.arrowCongr,
            DensityHalesJewett.concat, hi]
      | inr a =>
          simp [wordEquiv, coord, V, Equiv.arrowCongr,
            DensityHalesJewett.concat, hi]
    · simp [wordEquiv, coord, Equiv.arrowCongr,
        DensityHalesJewett.concat]
  have hfiber : fiber B (V₀ x) = fiber A (V x) := by
    ext y
    simp only [B, mem_fiber, A', Finset.mem_map_equiv]
    simp only [Equiv.symm_symm]
    rw [hword]
  rw [← hfiber]
  exact (sub_le_sub_right hz ε).trans (hV₀ x)

/-- A sufficient prefix size for finding a subspace above all of whose points the fibers remain
dense. -/
noncomputable def uniformFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ dimension ∧ 0 < ε ∧ ε < 1 then
    Nat.find (exists_eventually_uniformFibersFinSufficient alphabet dimension h.1 h.2.1 h.2.2)
  else 0

/-- The selected uniform-fibers bound satisfies the finite cardinal-model statement in every
larger prefix dimension. -/
lemma uniformFibersBound_fin_spec (alphabet dimension n : ℕ)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hn : uniformFibersBound alphabet dimension ε ≤ n) :
    UniformFibersFinSufficient alphabet dimension ε n := by
  classical
  rw [uniformFibersBound,
    dif_pos ⟨hdimension, hε₀, hε₁⟩] at hn
  exact Nat.find_spec
    (exists_eventually_uniformFibersFinSufficient alphabet dimension hdimension hε₀ hε₁) n hn

/-- Transport of uniform fibers is immediate for a subsingleton alphabet. -/
private lemma exists_fibers_dense_of_fin_sufficient_subsingleton
    {α ι κ : Type*} [Fintype α] [Fintype ι] [Subsingleton α]
    [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    (m : ℕ) (ε : ℝ)
    (hfin : UniformFibersFinSufficient (Fintype.card α) m ε (Fintype.card ι))
    (A : Finset (ι ⊕ κ → α)) (hA : ε < (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) α ι,
      ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A (V x)).dens : ℝ) := by
  classical
  by_cases hα : Nonempty α
  · letI : Nonempty α := hα
    have hε₁ : ε < 1 := hA.trans_le (by exact_mod_cast Finset.dens_le_one (s := A))
    obtain ⟨V₀, hV₀⟩ := hfin 0 Finset.univ (by simpa using hε₁)
    have hε₀ : 0 ≤ ε := by
      let x : Fin m → Fin (Fintype.card α) := fun _ ↦
        ⟨0, Fintype.card_pos_iff.mpr hα⟩
      have hx := hV₀ x
      have hfiber : fiber
          (Finset.univ : Finset (Fin (Fintype.card ι) ⊕ Fin 0 → Fin (Fintype.card α)))
          (V₀ x) = Finset.univ := by
        ext y
        simp [fiber]
      rw [hfiber] at hx
      simp only [Finset.dens_univ, sub_le_iff_le_add] at hx
      linarith
    have hApos : 0 < (A.dens : ℚ≥0) := by
      exact_mod_cast hε₀.trans_lt hA
    obtain ⟨w, hw⟩ := Finset.dens_pos.mp hApos
    have hAuniv : A = Finset.univ := by
      ext z
      simp only [Finset.mem_univ, iff_true]
      exact (Subsingleton.elim z w) ▸ hw
    let eα := Fintype.equivFin α
    let eι := Fintype.equivFin ι
    let V := V₀.reindex (Equiv.refl _) eα.symm eι.symm
    refine ⟨V, ?_⟩
    intro x
    rw [hAuniv]
    have hfiber : fiber (Finset.univ : Finset (ι ⊕ κ → α)) (V x) = Finset.univ := by
      ext y
      simp [fiber]
    rw [hfiber]
    simp only [Finset.dens_univ, sub_le_iff_le_add]
    linarith
  · letI : IsEmpty α := not_nonempty_iff.mp hα
    by_cases hκ : Nonempty (κ → α)
    · letI : IsEmpty κ := ⟨fun i ↦ isEmptyElim (Classical.choice hκ i)⟩
      letI : Fintype κ := Fintype.ofIsEmpty
      let eα := Fintype.equivFin α
      let eι := Fintype.equivFin ι
      let eκ := Fintype.equivFin κ
      let eCoord := Equiv.sumCongr eι eκ
      let eWord := eCoord.arrowCongr eα
      let A' := A.map eWord.toEmbedding
      have hA' : ε < (A'.dens : ℝ) := by
        simpa only [A', Finset.dens_map_equiv] using hA
      obtain ⟨V₀, hV₀⟩ := hfin (Fintype.card κ) A' hA'
      let V := V₀.reindex (Equiv.refl _) eα.symm eι.symm
      refine ⟨V, ?_⟩
      intro x
      let eSuffix := eκ.arrowCongr eα
      have hword (y : Fin (Fintype.card κ) → Fin (Fintype.card α)) :
          eWord.symm (DensityHalesJewett.concat (V₀ (eα ∘ x)) y) =
            DensityHalesJewett.concat (V x) (eSuffix.symm y) := by
        funext z
        cases z with
        | inl i =>
            simp [eWord, eCoord, eSuffix, V, Equiv.arrowCongr,
              DensityHalesJewett.concat]
        | inr i =>
            simp [eWord, eCoord, eSuffix, V, Equiv.arrowCongr,
              DensityHalesJewett.concat]
      have hfiber :
          fiber A' (V₀ (eα ∘ x)) =
            (fiber A (V x)).map eSuffix.toEmbedding := by
        ext y
        simp only [Finset.mem_map_equiv, mem_fiber, A']
        rw [hword]
      have hdens :
          ((fiber A' (V₀ (eα ∘ x))).dens : ℝ) =
            ((fiber A (V x)).dens : ℝ) := by
        rw [hfiber, Finset.dens_map_equiv]
      rw [← hdens]
      simpa only [A', Finset.dens_map_equiv] using hV₀ (eα ∘ x)
    · letI : IsEmpty (κ → α) := not_nonempty_iff.mp hκ
      letI : IsEmpty (ι ⊕ κ → α) := ⟨fun f ↦ isEmptyElim (fun i ↦ f (Sum.inr i))⟩
      have hAempty : A = ∅ := Subsingleton.elim _ _
      have hε : ε < 0 := by
        rw [hAempty] at hA
        norm_num at hA ⊢
        exact hA
      obtain ⟨V₀, hV₀⟩ := hfin 0
        (∅ : Finset (Fin (Fintype.card ι) ⊕ Fin 0 → Fin (Fintype.card α)))
        (by norm_num; exact hε)
      have hparam : IsEmpty (Fin m → Fin (Fintype.card α)) := by
        apply not_nonempty_iff.mp
        intro h
        have hx := hV₀ (Classical.choice h)
        have hfiber : fiber
            (∅ : Finset (Fin (Fintype.card ι) ⊕ Fin 0 → Fin (Fintype.card α)))
            (V₀ (Classical.choice h)) = ∅ := by
          ext y
          simp [fiber]
        rw [hfiber] at hx
        have : 0 - ε ≤ 0 := by
          norm_num at hx ⊢
          exact hx
        linarith
      letI := hparam
      let eα := Fintype.equivFin α
      let eι := Fintype.equivFin ι
      let V := V₀.reindex (Equiv.refl _) eα.symm eι.symm
      refine ⟨V, ?_⟩
      intro x
      exact isEmptyElim (eα ∘ x)

/-- Uniform fibers over finite cardinal models transport to arbitrary finite alphabets, prefix
coordinates, and suffix coordinates. -/
lemma exists_fibers_dense_of_fin_sufficient
    {α ι κ : Type*} [Fintype α] [Fintype ι]
    [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    (m : ℕ) (ε : ℝ)
    (hfin : UniformFibersFinSufficient (Fintype.card α) m ε (Fintype.card ι))
    (A : Finset (ι ⊕ κ → α)) (hA : ε < (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) α ι,
      ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A (V x)).dens : ℝ) := by
  classical
  cases subsingleton_or_nontrivial α with
  | inl hα =>
      letI : Subsingleton α := hα
      exact exists_fibers_dense_of_fin_sufficient_subsingleton m ε hfin A hA
  | inr hα =>
      letI : Nontrivial α := hα
      let a : α := Classical.choice inferInstance
      let b : α := Classical.choose (exists_ne a)
      have hab : b ≠ a := Classical.choose_spec (exists_ne a)
      let encodeCoordinate : κ → (κ → α) := fun i j ↦ if j = i then b else a
      have hencode : Function.Injective encodeCoordinate := by
        intro i j hij
        by_contra h
        have := congrFun hij i
        simp only [encodeCoordinate, if_pos, if_neg h] at this
        exact hab this
      letI : Finite κ := Finite.of_injective encodeCoordinate hencode
      letI := Fintype.ofFinite κ
      let eα := Fintype.equivFin α
      let eι := Fintype.equivFin ι
      let eκ := Fintype.equivFin κ
      let eCoord := Equiv.sumCongr eι eκ
      let eWord := eCoord.arrowCongr eα
      let A' := A.map eWord.toEmbedding
      have hA' : ε < (A'.dens : ℝ) := by
        simpa only [A', Finset.dens_map_equiv] using hA
      obtain ⟨V₀, hV₀⟩ := hfin (Fintype.card κ) A' hA'
      let V := V₀.reindex (Equiv.refl _) eα.symm eι.symm
      refine ⟨V, ?_⟩
      intro x
      let eSuffix := eκ.arrowCongr eα
      have hword (y : Fin (Fintype.card κ) → Fin (Fintype.card α)) :
          eWord.symm (DensityHalesJewett.concat (V₀ (eα ∘ x)) y) =
            DensityHalesJewett.concat (V x) (eSuffix.symm y) := by
        funext z
        cases z with
        | inl i =>
            simp [eWord, eCoord, eSuffix, V, Equiv.arrowCongr,
              DensityHalesJewett.concat]
        | inr i =>
            simp [eWord, eCoord, eSuffix, V, Equiv.arrowCongr,
              DensityHalesJewett.concat]
      have hfiber :
          fiber A' (V₀ (eα ∘ x)) =
            (fiber A (V x)).map eSuffix.toEmbedding := by
        ext y
        simp only [Finset.mem_map_equiv, mem_fiber, A']
        rw [hword]
      have hdens :
          ((fiber A' (V₀ (eα ∘ x))).dens : ℝ) =
            ((fiber A (V x)).dens : ℝ) := by
        rw [hfiber, Finset.dens_map_equiv]
      rw [← hdens]
      simpa only [A', Finset.dens_map_equiv] using hV₀ (eα ∘ x)

/-- Uniform fibers on a subspace. -/
lemma exists_fibers_dense {α ι κ : Type*} [Fintype α] [Fintype ι]
    [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hι : uniformFibersBound (Fintype.card α) m ε ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → α)) (hA : ε < (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) α ι,
      ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A (V x)).dens : ℝ) := by
  exact exists_fibers_dense_of_fin_sufficient m ε
    (uniformFibersBound_fin_spec (Fintype.card α) m (Fintype.card ι) hm hε₀ hε₁ hι)
    A hA

/-- Finiteness of the full word space supplies finiteness of its suffix word space. -/
@[instance_reducible]
noncomputable def suffixFunctionFintype (α ι κ : Type*)
    [Fintype (ι ⊕ κ → α)] : Fintype (κ → α) := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    by_cases hα : Nonempty α
    · letI : Inhabited α := ⟨Classical.choice hα⟩
      exact Fintype.ofInjective (fun y ↦ DensityHalesJewett.concat (fun _ ↦ default) y)
        fun y z h ↦ by
          funext c
          change DensityHalesJewett.concat (fun _ : ι ↦ default) y =
            DensityHalesJewett.concat (fun _ ↦ default) z at h
          exact congrFun h (Sum.inr c)
    · letI : IsEmpty α := not_nonempty_iff.mp hα
      by_cases hκ : Nonempty (κ → α)
      · letI : Inhabited (κ → α) := ⟨Classical.choice hκ⟩
        exact Fintype.ofSubsingleton default
      · letI : IsEmpty (κ → α) := not_nonempty_iff.mp hκ
        exact Fintype.ofIsEmpty
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    exact Fintype.ofInjective (fun y z ↦ Sum.elim (fun a : ι ↦ isEmptyElim a) y z) fun y z h ↦ by
      funext c
      change (fun w ↦ Sum.elim (fun a : ι ↦ isEmptyElim a) y w) =
        (fun w ↦ Sum.elim (fun a : ι ↦ isEmptyElim a) z w) at h
      exact congrFun h (Sum.inr c)

/-- Averaging restricted-parameter slice densities over suffixes equals averaging their ambient
fiber densities over restricted parameter words. -/
lemma average_restrictedParameterSlice {k M : ℕ}
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) :
    Finset.expect Finset.univ (fun y : κ → Fin (k + 1) ↦
      ((Finset.univ.filter fun x : Fin M → Fin k ↦
        DensityHalesJewett.concat (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) =
      Finset.expect Finset.univ (fun x : Fin M → Fin k ↦
        ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) := by
  simp_rw [← Finset.expect_indicator_one]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  refine Finset.expect_congr rfl fun y _ ↦ ?_
  by_cases h : DensityHalesJewett.concat (W (Fin.castSucc ∘ x)) y ∈ A
  · have hx : x ∈ Finset.univ.filter fun z : Fin M → Fin k ↦
        DensityHalesJewett.concat (W (Fin.castSucc ∘ z)) y ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hy : y ∈ fiber A (W (Fin.castSucc ∘ x)) := mem_fiber.mpr h
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    simp only [Pi.one_apply]
  · have hx : x ∉ Finset.univ.filter fun z : Fin M → Fin k ↦
        DensityHalesJewett.concat (W (Fin.castSucc ∘ z)) y ∈ A :=
      fun hx ↦ h (Finset.mem_filter.mp hx).2
    have hy : y ∉ fiber A (W (Fin.castSucc ∘ x)) := fun hy ↦ h (mem_fiber.mp hy)
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

/-- Averaging a pointwise-dense family of suffix fibers produces one suffix above which the
restricted parameter family is dense. -/
lemma exists_dense_suffix_of_restricted_fibers {k M : ℕ} (hk : 0 < k) (δ : ℝ)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hW : ∀ x : Fin M → Fin k,
      δ / 2 ≤ ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) :
    ∃ y : κ → Fin (k + 1),
      δ / 2 ≤
        ((Finset.univ.filter fun x : Fin M → Fin k ↦
          DensityHalesJewett.concat (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have havg : δ / 2 ≤
      Finset.expect Finset.univ (fun y : κ → Fin (k + 1) ↦
        ((Finset.univ.filter fun x : Fin M → Fin k ↦
          DensityHalesJewett.concat (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) := by
    rw [average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty fun x _ ↦ hW x
  by_contra h
  push Not at h
  apply (not_lt_of_ge havg)
  apply Finset.expect_lt
  · intro y _
    exact (h y).le
  · exact ⟨fun _ ↦ 0, Finset.mem_univ _, h (fun _ ↦ 0)⟩

/-- Extend a restricted parameter subspace to the full alphabet, attach a fixed suffix, and
transport the resulting subspace along an equivalence of ambient coordinates. -/
lemma extend_restricted_subspace {k m M : ℕ} {ι κ ζ : Type*}
    [DecidableEq (ζ → Fin (k + 1))] (e : ι ⊕ κ ≃ ζ)
    (A : Finset (ζ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) (y : κ → Fin (k + 1))
    (S : Combinatorics.Subspace (Fin m) (Fin k) (Fin M))
    (hS : ∀ x, (DensityHalesJewett.concat (W (Fin.castSucc ∘ S x)) y) ∘ e.symm ∈ A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ,
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  let lift_S : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M) :=
    { idxFun := fun i ↦ (S.idxFun i).map (Fin.castSuccEmb : Fin k → Fin (k + 1)) id
      proper := fun e ↦ by
        obtain ⟨i, hi⟩ := S.proper e
        refine ⟨i, ?_⟩
        simp [hi] }
  have h_lift_eval (x : Fin m → Fin k) : lift_S (Fin.castSuccEmb ∘ x) = Fin.castSucc ∘ S x := by
    ext i
    simp [lift_S, Combinatorics.Subspace.coe_apply]
    cases S.idxFun i <;> simp
  let concat_suffix : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ζ :=
    { idxFun := fun c ↦
        match e.symm c with
        | Sum.inl i => W.idxFun i
        | Sum.inr j => Sum.inl (y j)
      proper := fun e' ↦ by
        obtain ⟨i, hi⟩ := W.proper e'
        refine ⟨e (Sum.inl i), ?_⟩
        simp [hi] }
  have h_concat_suffix_eval (z : Fin M → Fin (k + 1)) :
      concat_suffix z = (DensityHalesJewett.concat (W z) y) ∘ e.symm := by
    ext c
    simp only [Subspace.coe_apply, DensityHalesJewett.concat, Function.comp_apply, concat_suffix]
    cases e.symm c with
    | inl i => simp [Combinatorics.Subspace.coe_apply]
    | inr j => simp
  let V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ :=
    compose concat_suffix lift_S
  refine ⟨V, ?_⟩
  intro w hw
  rw [restrictAlphabet, Finset.mem_image] at hw
  rcases hw with ⟨x, _, rfl⟩
  rw [compose_apply, h_lift_eval x, h_concat_suffix_eval (Fin.castSucc ∘ S x)]
  exact hS x

/-- For the empty restricted alphabet, the restricted range is empty as soon as the parameter
dimension is positive. -/
lemma exists_empty_restrictAlphabet_subset {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Finset (Fin n → Fin 1)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  let V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n) :=
    { idxFun := fun i ↦ if hi : i.val < m then Sum.inr ⟨i.val, hi⟩ else Sum.inl 0
      proper := fun e ↦ by
        refine ⟨Fin.castLE hmn e, ?_⟩
        simp only [Fin.castLE, e.isLt, ↓reduceDIte] }
  refine ⟨V, ?_⟩
  intro w hw
  rw [restrictAlphabet] at hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨x, _⟩ := hw
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)

/-- The restricted-alphabet conclusion holds in every sufficiently large dimension. -/
lemma exists_eventually_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
      δ * (k + 1 : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n hmn A _
    exact exists_empty_restrictAlphabet_subset hm hmn A
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  let M := max 1 (densityBound k m (δ / 2))
  refine ⟨variableCutFibersBound (k + 1) M (δ / 2), ?_⟩
  intro n hn A hA
  have hM : 1 ≤ M := le_max_left _ _
  have hA' : δ ≤ (A.dens : ℝ) := by
    refine density_le_of_card_le (Nat.zero_lt_succ k) δ A ?_
    convert hA using 1
    norm_num
  obtain ⟨p, q, e, _hq, W, hW⟩ :=
    variableCutFibersBound_spec (k + 1) M n hM (by linarith) hn A
  obtain ⟨y, hy⟩ :=
    exists_dense_suffix_of_restricted_fibers hk δ (splitWords e A) W fun x ↦ by
      linarith [hW (Fin.castSucc ∘ x)]
  let B := Finset.univ.filter fun x : Fin M → Fin k ↦
    DensityHalesJewett.concat (W (Fin.castSucc ∘ x)) y ∈ splitWords e A
  obtain ⟨S, hS⟩ :=
    exists_of_density hDHJ m hm (δ / 2) (by linarith) M (le_max_right _ _) B
      (card_le_of_density_le hk (δ / 2) B (by simpa only [B] using hy))
  refine extend_restricted_subspace e A W y S ?_
  intro x
  rw [← mem_splitWords]
  simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hS x

/-- A bound for the restricted-alphabet subspace lemma. -/
noncomputable def restrictAlphabetBound (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ HasDensityHJ k then
    Nat.find (exists_eventually_restrictAlphabet_subset h.2.2 m h.1 δ h.2.1)
  else 0

lemma restrictAlphabetBound_spec {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  rw [restrictAlphabetBound, dif_pos ⟨hm, hδ, hDHJ⟩] at hn
  exact Nat.find_spec (exists_eventually_restrictAlphabet_subset hDHJ m hm δ hδ) n hn A hA

/-- A dense family over `Fin (k+1)` contains the `Fin k` restriction of a subspace. -/
lemma exists_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1)))
    (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  exact restrictAlphabetBound_spec hDHJ m hm δ hδ n hn A hA

end Subspace
end DensityHalesJewett

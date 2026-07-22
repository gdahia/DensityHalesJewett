/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.GrahamRothschild
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

/-- A sufficient prefix size for finding a subspace above all of whose points the fibers remain
dense. -/
opaque uniformFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ

/-- Uniform fibers on a subspace. -/
lemma exists_fibers_dense {α ι κ : Type*} [Fintype α] [Fintype ι]
    [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hι : uniformFibersBound (Fintype.card α) m ε ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → α)) (hA : ε < (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) α ι,
      ∀ x, (A.dens : ℝ) - ε ≤ ((fiber A (V x)).dens : ℝ) := by
  sorry

/-- A bound for the restricted-alphabet subspace lemma. -/
opaque restrictAlphabetBound (k m : ℕ) (δ : ℝ) : ℕ

/-- A dense family over `Fin (k+1)` contains the `Fin k` restriction of a subspace. -/
lemma exists_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1)))
    (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  sorry

end Subspace
end DensityHalesJewett

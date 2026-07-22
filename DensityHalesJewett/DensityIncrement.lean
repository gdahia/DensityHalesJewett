/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Insensitive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The density-increment dichotomy

Numerical parameters, correlated fibers, structured correlation, and the density increment
proposition.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

namespace Parameters

/-- A positive dimension selected from the density Hales--Jewett assertion when available. -/
noncomputable def m₀ (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.succ <| Nat.find <| h.2 (δ / 4) (by linarith)
  else 1

lemma m₀_pos (k : ℕ) (δ : ℝ) : 0 < m₀ k δ := by
  classical
  unfold m₀
  split <;> simp

/-- The selected dimension is antitone in the density threshold. -/
lemma m₀_antitone {k : ℕ} (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : m₀ k ρ ≤ m₀ k δ := by
  classical
  rw [m₀, dif_pos ⟨hδ.trans_le hδρ, hDHJ⟩, m₀, dif_pos ⟨hδ, hDHJ⟩]
  apply Nat.succ_le_succ
  apply Nat.find_min'
  intro n hn A hA
  refine Nat.find_spec (hDHJ (δ / 4) (by linarith)) n hn A (le_trans (by gcongr) hA)

/-- The denominator in the parameter definition grows with the selected dimension. -/
lemma power_difference_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m ≤
      ((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    refine ih.trans ?_
    rw [Nat.cast_add, Nat.cast_one]
    suffices 0 ≤ (k : ℝ) * (((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n) by
      rw [Nat.cast_add, Nat.cast_one] at this
      nlinarith [pow_nonneg (by positivity : 0 ≤ (k : ℝ)) n]
    apply mul_nonneg
    · positivity
    · apply sub_nonneg.mpr
      apply pow_le_pow_left₀
      · positivity
      · exact_mod_cast Nat.le_succ k

/-- The denominator defining `θ` is positive for every admissible alphabet and density. -/
lemma θ_denominator_pos {k : ℕ} (hk : 2 ≤ k) (δ : ℝ) :
    0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
  apply sub_pos.mpr
  apply pow_lt_pow_left₀
  · exact_mod_cast Nat.lt_succ_self k
  · positivity
  · exact Nat.ne_of_gt <| m₀_pos k δ

/-- The correlated-fibers threshold attached to an alphabet size and density. -/
noncomputable def θ (k : ℕ) (δ : ℝ) : ℝ :=
  (δ / 4) /
    (((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ)

/-- The threshold is monotone in the density parameter. -/
lemma θ_mono_of_dhj {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  unfold θ
  refine div_le_div₀ ?_ (by linarith) (θ_denominator_pos hk ρ) ?_
  · exact div_nonneg (hδ.trans_le hδρ).le (by norm_num)
  · exact power_difference_mono k <| m₀_antitone hDHJ hδ hδρ

/-- The threshold is monotone even when the density Hales--Jewett assertion is unavailable. -/
lemma θ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  classical
  by_cases hDHJ : HasDensityHJ k
  · exact θ_mono_of_dhj hk hDHJ hδ hδρ
  · unfold θ
    rw [m₀, dif_neg (fun h ↦ hDHJ h.2), m₀, dif_neg (fun h ↦ hDHJ h.2)]
    apply div_le_div_of_nonneg_right
    · linarith
    · rw [pow_one, pow_one, Nat.cast_add, Nat.cast_one]
      linarith

lemma θ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < θ k δ := by
  unfold θ
  exact div_pos (by positivity) (θ_denominator_pos hk δ)

/-- The error tolerance attached to an alphabet size and density. -/
noncomputable def η (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))

/-- The error tolerance is monotone in the density parameter. -/
lemma η_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : η k δ ≤ η k ρ := by
  unfold η
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ (θ_mono hk hδ hδρ) (θ_pos hk hδ).le
        (hδ.trans_le hδρ).le
    · norm_num
  · exact div_le_div_of_nonneg_right (θ_mono hk hδ hδρ) (by norm_num)
  · exact div_le_div_of_nonneg_right hδρ (by norm_num)

lemma η_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < η k δ := by
  unfold η
  apply lt_min
  · positivity [θ_pos hk hδ]
  · apply lt_min
    · positivity [θ_pos hk hδ]
    · positivity

/-- The density increment attached to an alphabet size and density. -/
noncomputable def γ (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * η k δ ^ 2 / k) (min (η k δ ^ 2 / 2) (3 * η k δ))

/-- The increment is monotone in the density parameter. -/
lemma γ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : γ k δ ≤ γ k ρ := by
  unfold γ
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · apply mul_le_mul hδρ
      · exact (sq_le_sq₀ (η_pos hk hδ).le
          (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
      · positivity
      · exact (hδ.trans_le hδρ).le
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact (sq_le_sq₀ (η_pos hk hδ).le
        (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
    · norm_num
  · exact mul_le_mul_of_nonneg_left (η_mono hk hδ hδρ) (by norm_num)

lemma γ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < γ k δ := by
  unfold γ
  positivity [η_pos hk hδ]

lemma η_lt_θ_div_two {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    η k δ < θ k δ / 2 := by
  unfold η
  refine lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) ?_
  linarith [θ_pos hk hδ]

lemma η_le_δ_div_six (k : ℕ) (δ : ℝ) : η k δ ≤ δ / 6 := by
  unfold η
  exact (min_le_right _ _).trans (min_le_right _ _)

lemma γ_le_η_sq_div_two (k : ℕ) (δ : ℝ) : γ k δ ≤ η k δ ^ 2 / 2 := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma γ_le_three_mul_η (k : ℕ) (δ : ℝ) : γ k δ ≤ 3 * η k δ := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The increment parameters can be chosen uniformly above a fixed positive density floor. -/
lemma γ_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < γ k δ₀ ∧ ∀ ρ, δ₀ ≤ ρ → γ k δ₀ ≤ γ k ρ := by
  refine ⟨γ_pos hk hδ₀, ?_⟩
  intro ρ hδρ
  exact γ_mono hk hδ₀ hδρ

end Parameters

/-- A finite word family contains no complete combinatorial line. -/
def IsLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A

/-- Pull a word family back to the parameter cube of a subspace. -/
def pullback {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι → α)) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ V x ∈ A

/-- A bound for the correlated-fibers lemma. -/
opaque correlatedFibersBound (k m : ℕ) (δ : ℝ) : ℕ

/-- **Hard helper:** uniformize the fibers and canonize their line-density coloring.

The working parameter dimension is chosen large enough both for the requested `m`-dimensional
output and for the density Hales--Jewett argument at dimension `Parameters.m₀ k δ`.  In the
monochromatic good case, restrict the working subspace to `m` parameters.  In the bad case, retain
the larger subspace as a certificate whose every restricted-alphabet line has common-suffix density
strictly below `Parameters.θ k δ`. -/
lemma exists_correlated_fibers_or_sparse_certificate {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hι : correlatedFibersBound k m δ ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
      ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
        ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
          (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin M),
            ((Finset.univ.filter fun y ↦
              ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
                Parameters.θ k δ := by
  sorry

/-- **Hard helper:** the uniformly sparse certificate is impossible.

Average the dense fibers over suffixes, find many suffix slices of density at least `δ / 4`, and
apply `hDHJ` on an embedded `Parameters.m₀ k δ`-dimensional parameter cube in each such slice.
Pigeonholing the resulting lines gives one line with common-suffix density at least
`Parameters.θ k δ`, contradicting the certificate. -/
lemma not_exists_sparse_correlated_fibers_certificate {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    ¬ ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
      ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
        (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
        ∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ := by
  sorry

/-- Every parameter-cube line in a suitable subspace has a dense common fiber. -/
lemma exists_subspace_correlated_fibers {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hι : correlatedFibersBound k m δ ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦ ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  obtain hV | hsparse :=
    exists_correlated_fibers_or_sparse_certificate hk hDHJ m hm δ hδ₀ hδ₁ hι A hA
  · exact hV
  · exact (not_exists_sparse_correlated_fibers_certificate hk hDHJ δ hδ₀ hδ₁ A
      hsparse).elim

/-- The pullback of a word family to a subspace after fixing the suffix coordinates. -/
def suffixPullback {α η ι κ : Type*} [Fintype (η → α)]
    [DecidableEq (ι ⊕ κ → α)] (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι ⊕ κ → α)) (y : κ → α) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ concat (V x) y ∈ A

/-- The parameter lines whose first-`k` points belong to a word family at a fixed suffix. -/
def suffixLines {k m : ℕ} {ι κ : Type*}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (y : κ → Fin (k + 1)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter fun l ↦ ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A

/-- Fix suffix coordinates of a subspace. -/
def Subspace.fixSuffix {α η ι κ : Type*} (V : Combinatorics.Subspace η α ι)
    (y : κ → α) : Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun := Sum.elim V.idxFun (Sum.inl ∘ y)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

/-- Fix suffix coordinates and transport the ambient coordinates along an equivalence. -/
def Subspace.fixSuffixReindex {α η ι κ ζ : Type*} (e : ι ⊕ κ ≃ ζ)
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α ζ :=
  (Subspace.fixSuffix V y).reindex (Equiv.refl _) (Equiv.refl _) e

/-- Pointwise fiber lower bounds imply the corresponding average lower bound for fixed-suffix
pullbacks.  This is a finite double-counting argument. -/
lemma average_suffixPullback_lower {α η ι κ : Type*} [Nonempty α] [Fintype (η → α)]
    [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) (r : ℝ)
    (hV : ∀ x, r ≤ ((fiber A (V x)).dens : ℝ)) :
    r ≤ 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) =
      𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
    calc
      𝔼 x : η → α, ((fiber A (V x)).dens : ℝ)
          = 𝔼 x : η → α, 𝔼 y : κ → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        simp
      _ = 𝔼 y : κ → α, 𝔼 x : η → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (η → α)) (Finset.univ : Finset (κ → α))]
      _ = 𝔼 y : κ → α, 𝔼 x : η → α,
          (Set.indicator (suffixPullback V A y) (1 : (η → α) → ℝ) x : ℝ) := by
        refine Finset.expect_congr rfl fun y _ => ?_
        refine Finset.expect_congr rfl fun x _ => ?_
        by_cases h : concat (V x) y ∈ A
        · have hy : y ∈ fiber A (V x) := by simpa [fiber] using h
          have hx : x ∈ suffixPullback V A y := by
            dsimp [suffixPullback]
            simp [h]
          simp [hy, hx]
        · have hy : y ∉ fiber A (V x) := by simpa [fiber] using h
          have hx : x ∉ suffixPullback V A y := by
            dsimp [suffixPullback]
            simp [h]
          simp [hy, hx]
      _ = 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
        simp
  have h_r_le_expect : r ≤ 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := η → α)) fun x _ => hV x
  exact h_r_le_expect.trans h_expect_eq.le

/-- If a bounded function has average at least `δ - η²/2` but never reaches
`δ + η²/2`, then it is at least `δ - 2η` on all but an `η`-fraction of its domain. -/
lemma density_near_average {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (δ η : ℝ) (hη₀ : 0 < η) (_hη₁ : η ≤ 1)
    (_hf₀ : ∀ x, 0 ≤ f x) (_hf₁ : ∀ x, f x ≤ 1)
    (havg : δ - η ^ 2 / 2 ≤ 𝔼 x : X, f x)
    (hupper : ∀ x, f x < δ + η ^ 2 / 2) :
    1 - η ≤ ((Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x).dens : ℝ) := by
  set H := Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x
  by_cases hH : 1 - η ≤ (H.dens : ℝ)
  · exact hH
  · exfalso
    have h_dens_H_lt : (H.dens : ℝ) < 1 - η := by linarith
    have h_pos : 0 < η ^ 2 / 2 + 2 * η := by nlinarith
    have hfg : ∀ x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η)
        * (Set.indicator H (1 : X → ℝ) x : ℝ) := by
      intro x
      by_cases hxH : x ∈ H
      · have h_indicator : (Set.indicator H (1 : X → ℝ) x : ℝ) = 1 := by simp [hxH]
        simp [h_indicator]
        linarith [hupper x]
      · have hx_lt : f x < δ - 2 * η := by
          have : ¬(δ - 2 * η ≤ f x) := by simpa [H] using hxH
          linarith
        have h_indicator : (Set.indicator H (1 : X → ℝ) x : ℝ) = 0 := by simp [hxH]
        simp [h_indicator]
        linarith
    have h_expect_f_le_expect_g : 𝔼 x : X, f x ≤ 𝔼 x : X, ((δ - 2 * η : ℝ) + (η ^ 2 / 2 + 2 * η) *
        (Set.indicator H (1 : X → ℝ) x : ℝ)) :=
      Finset.expect_le_expect (fun x _ => hfg x)
    have h_expect_g : 𝔼 x : X, ((δ - 2 * η : ℝ) + (η ^ 2 / 2 + 2 * η) *
        (Set.indicator H (1 : X → ℝ) x : ℝ)) =
      (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by
      calc
        𝔼 x : X, ((δ - 2 * η : ℝ) + (η ^ 2 / 2 + 2 * η) * (Set.indicator H (1 : X → ℝ) x : ℝ)) =
          𝔼 x : X, (δ - 2 * η : ℝ) + 𝔼 x : X, ((η ^ 2 / 2 + 2 * η)
            * (Set.indicator H (1 : X → ℝ) x : ℝ)) := by
          rw [Finset.expect_add_distrib]
        _ = (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * 𝔼 x : X, (Set.indicator H (1 : X → ℝ) x : ℝ) := by
          rw [Finset.expect_const univ_nonempty, ← Finset.mul_expect]
        _ = (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by simp
    rw [h_expect_g] at h_expect_f_le_expect_g
    have h_upper_bound : (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) <
      (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * (1 - η) := by
      nlinarith
    nlinarith

/-- Dense common suffix fibers for every line give the same lower bound for the average
fixed-suffix line density.  This is the second finite double-counting step. -/
lemma average_suffixLines_lower {k m : ℕ} {ι κ : Type*}
    [Fintype (κ → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (θ : ℝ)
    (hV : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ ((Finset.univ.filter fun y ↦
        ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    θ ≤ 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) =
      𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
    calc
      𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)
          = 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
            𝔼 y : κ → Fin (k + 1),
            (Set.indicator (Finset.univ.filter fun y ↦
              ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A)
              (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        refine Finset.expect_congr rfl fun l _ => ?_
        rw [← Finset.expect_indicator_one]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A)
            (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (Combinatorics.Line (Fin k) (Fin m)))
          (Finset.univ : Finset (κ → Fin (k + 1)))]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (suffixLines V A y)
            (1 : Combinatorics.Line (Fin k) (Fin m) → ℝ) l : ℝ) := by
        refine Finset.expect_congr rfl fun y _ => ?_
        refine Finset.expect_congr rfl fun l _ => ?_
        dsimp [suffixLines]
        by_cases h : ∀ a : Fin k, concat (V (Fin.castSucc ∘ l a)) y ∈ A
        · simp [h]
        · simp [h]
      _ = 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
        simp
  have h_θ_le_expect : θ ≤ 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := Combinatorics.Line (Fin k) (Fin m)))
      fun l _ => hV l
  exact h_θ_le_expect.trans h_expect_eq.le

/-- A `[0,1]`-valued function with average at least `θ` exceeds `θ/2` on a set of
density at least `θ/2`. -/
lemma density_half_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1)
    (havg : θ ≤ 𝔼 x : X, f x) :
    θ / 2 ≤ ((Finset.univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) := by
  have hθ2_nonneg : 0 ≤ θ / 2 := by positivity
  have h_ge_threshold : (θ - θ / 2) / (1 - θ / 2) ≤
      ((Finset.univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) :=
    density_ge_threshold f θ (θ / 2) hf₀ hf₁ hθ2_nonneg (by linarith) havg
  have h_simplify : (θ - θ / 2) / (1 - θ / 2) = (θ / 2) / (1 - θ / 2) := by
    have hnum : θ - θ / 2 = θ / 2 := by ring
    rw [hnum]
  rw [h_simplify] at h_ge_threshold
  have h_half_le_div : θ / 2 ≤ (θ / 2) / (1 - θ / 2) := by
    have hpos : 0 < 1 - θ / 2 := by linarith
    rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg (θ / 2)]
  linarith

/-- Two subsets of densities at least `1-η` and `θ/2` intersect when `η < θ/2`. -/
lemma exists_mem_inter_of_large_density {X : Type*} [Fintype X]
    (S T : Finset X) (η θ : ℝ)
    (hS : 1 - η ≤ (S.dens : ℝ)) (hT : θ / 2 ≤ (T.dens : ℝ))
    (hηθ : η < θ / 2) : ∃ x, x ∈ S ∧ x ∈ T := by
  classical
  by_contra h
  have h_inter_empty : S ∩ T = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun x hx => h ⟨x, Finset.mem_inter.1 hx⟩
  have h_union_dens : ((S ∪ T).dens : ℝ) = (S.dens : ℝ) + (T.dens : ℝ) := by
    have h_disjoint : Disjoint S T :=
      Finset.disjoint_iff_inter_eq_empty.mpr h_inter_empty
    exact_mod_cast Finset.dens_union_of_disjoint h_disjoint
  have h_dens_le_one : ((S ∪ T).dens : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one (s := S ∪ T)
  linarith

/-- The correlated-fiber threshold is at most one in the admissible parameter range. -/
lemma Parameters.θ_le_one {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₁ : δ ≤ 1) :
    Parameters.θ k δ ≤ 1 := by
  unfold θ
  have hden_pos : 0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ :=
    θ_denominator_pos hk δ
  have hm₀_pos : 0 < m₀ k δ := m₀_pos k δ
  have h_one_le_diff : 1 ≤ ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
    have h1 : ((k + 1 : ℕ) : ℝ) ^ 1 - (k : ℝ) ^ 1 = (1 : ℝ) := by norm_num
    simpa [h1] using power_difference_mono k (Nat.succ_le_of_lt hm₀_pos)
  refine (div_le_one hden_pos).mpr ?_
  linarith

/-- Correlated fibers yield either a dense fixed suffix or a fixed suffix supporting many
complete parameter lines. -/
lemma exists_suffix_many_lines {k m : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (Fin m → Fin (k + 1))]
    [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (hfiber : ∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    (∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤
      ((suffixPullback V A y).dens : ℝ)) ∨
    ∃ y, δ - 2 * Parameters.η k δ ≤ ((suffixPullback V A y).dens : ℝ) ∧
      Parameters.θ k δ / 2 ≤ ((suffixLines V A y).dens : ℝ) := by
  classical
  let f := fun y : κ → Fin (k + 1) ↦ ((suffixPullback V A y).dens : ℝ)
  let g := fun y : κ → Fin (k + 1) ↦ ((suffixLines V A y).dens : ℝ)
  by_cases hinc : ∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤ f y
  · exact Or.inl hinc
  refine Or.inr ?_
  have hη₀ : 0 < Parameters.η k δ := Parameters.η_pos hk hδ₀
  have hη₁ : Parameters.η k δ ≤ 1 :=
    (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  have havgf : δ - Parameters.η k δ ^ 2 / 2 ≤ 𝔼 y, f y := by
    exact average_suffixPullback_lower V A _ hfiber
  have hupper : ∀ y, f y < δ + Parameters.η k δ ^ 2 / 2 := by
    intro y
    exact lt_of_not_ge fun hy ↦ hinc ⟨y, hy⟩
  have hmostly : 1 - Parameters.η k δ ≤
      ((Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y).dens : ℝ) := by
    refine density_near_average f δ (Parameters.η k δ) hη₀ hη₁ ?_ ?_ havgf hupper
    · intro y
      dsimp only [f]
      positivity
    · intro y
      dsimp only [f]
      exact_mod_cast Finset.dens_le_one (s := suffixPullback V A y)
  have havgg : Parameters.θ k δ ≤ 𝔼 y, g y := by
    exact average_suffixLines_lower V A (Parameters.θ k δ) hlines
  have hmany : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y).dens : ℝ) := by
    refine density_half_threshold g (Parameters.θ k δ) (Parameters.θ_pos hk hδ₀)
      (Parameters.θ_le_one hk hδ₁) ?_ ?_ havgg
    · intro y
      dsimp only [g]
      positivity
    · intro y
      dsimp only [g]
      exact_mod_cast Finset.dens_le_one (s := suffixLines V A y)
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_inter_of_large_density
    (Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y)
    (Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y)
    (Parameters.η k δ) (Parameters.θ k δ) hmostly hmany
    (Parameters.η_lt_θ_div_two hk hδ₀)
  refine ⟨y, ?_, ?_⟩
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f] using hy₁
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g] using hy₂

/-- Fixing a suffix and reindexing preserves the relative-density and complete-line statistics.
The proof is coordinate bookkeeping using `Subspace.reindex_apply` and `Finset.mem_map_equiv`. -/
lemma Subspace.fixSuffixReindex_statistics {k m : ℕ} {ι κ ζ : Type*}
    [Fintype (Fin m → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ζ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (e : ι ⊕ κ ≃ ζ) (A : Finset (ζ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (y : κ → Fin (k + 1)) :
    let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
    (Subspace.relativeDensity (Subspace.fixSuffixReindex e V y) A : ℝ) =
        ((suffixPullback V A' y).dens : ℝ) ∧
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, Subspace.fixSuffixReindex e V y (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) =
        ((suffixLines V A' y).dens : ℝ) := by
  sorry

/-- A bound for the many-lines lemma. -/
def manyLinesBound (k m : ℕ) (δ : ℝ) : ℕ :=
  correlatedFibersBound k m δ

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
lemma exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * Parameters.η k δ ≤ (Subspace.relativeDensity V A : ℝ) ∧
      Parameters.θ k δ / 2 ≤
        ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  classical
  let p := correlatedFibersBound k m δ
  let q := n - p
  have hpn : p ≤ n := by
    simpa only [manyLinesBound, p] using hn
  have hpq : p + q = n := Nat.add_sub_of_le hpn
  let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
  let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
  have hA' : δ ≤ (A'.dens : ℝ) := by
    simpa only [A', Finset.dens_map_equiv] using hA
  obtain ⟨W, hWfiber, hWlines⟩ :=
    exists_subspace_correlated_fibers hk hDHJ m hm δ hδ₀ hδ₁
      (ι := Fin p) (κ := Fin q) (by
        simp only [Fintype.card_fin]
        exact le_rfl) A' hA'
  obtain ⟨y, hy⟩ | ⟨y, hy, hylines⟩ :=
    exists_suffix_many_lines hk δ hδ₀ hδ₁ A' W hWfiber hWlines
  · refine Or.inl ⟨Subspace.fixSuffixReindex e W y, ?_⟩
    rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
    simpa only [A'] using hy
  · refine Or.inr ⟨Subspace.fixSuffixReindex e W y, ?_, ?_⟩
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
      simpa only [A'] using hy
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).2]
      simpa only [A'] using hylines

/-- A parameter-cube dimension sufficient for the insensitive-intersection construction. -/
opaque insensitiveIntersectionDimension (k : ℕ) (δ : ℝ) : ℕ

/-- Many complete restricted-alphabet lines yield a large insensitive intersection whose part
inside a line-free family is small.  This packages the endpoint construction, its injective
line count, the identification of the intersection, and the geometric-decay estimate. -/
lemma exists_endpoint_insensitive_intersection {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
      Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
      ((pullback V A ∩ IsInsensitive.intersection C).dens : ℝ) ≤
        Parameters.η k δ := by
  sorry

/-- The numerical parameters turn the absolute density left outside a large intersection into
the required relative density gain. -/
lemma Parameters.large_intersection_complement_gain {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    (δ + 6 * η k δ) * (1 - θ k δ / 4) ≤ δ - 3 * η k δ := by
  have hη : η k δ ≤ δ * θ k δ / 48 :=
    min_le_left (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))
  have hθ := θ_pos hk hδ₀
  nlinarith [mul_nonneg hδ₀.le hθ.le, η_pos hk hδ₀,
    mul_nonneg (η_pos hk hδ₀).le hθ.le]

/-- Removing an intersection of density at least `θ / 4`, while losing at most `η` of a family
of density `δ - 2η`, gives the two complement estimates used below. -/
lemma density_complement_bounds {X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq X] (A C : Finset X) (δ η θ : ℝ)
    (hδ₀ : 0 ≤ δ) (hη₀ : 0 ≤ η) (hA : δ - 2 * η ≤ (A.dens : ℝ))
    (hC : θ / 4 ≤ (C.dens : ℝ))
    (hAC : ((A ∩ C).dens : ℝ) ≤ η)
    (hgain : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η) :
    (δ + 6 * η) * ((Cᶜ).dens : ℝ) ≤ ((A ∩ Cᶜ).dens : ℝ) ∧
      δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
  have hsplitA : ((A ∩ C).dens : ℝ) + ((A ∩ Cᶜ).dens : ℝ) = (A.dens : ℝ) := by
    norm_cast
    simpa only [sdiff_eq_inter_compl] using Finset.dens_inter_add_dens_sdiff A C
  have houtside : δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
    linarith
  have hsplitC : ((Cᶜ).dens : ℝ) + (C.dens : ℝ) = 1 := by
    norm_cast
    simpa only [← compl_eq_univ_sdiff, Finset.dens_univ] using
      Finset.dens_sdiff_add_dens_eq_dens C.subset_univ
  refine ⟨(mul_le_mul_of_nonneg_left ?_ ?_).trans (hgain.trans houtside), houtside⟩
  · linarith
  · nlinarith

/-- A large intersection of insensitive families with a density gain on its complement. -/
lemma exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A)
    (hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (Subspace.relativeDensity V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
        Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
        (δ + 6 * Parameters.η k δ) *
            ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
        δ - 3 * Parameters.η k δ ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  classical
  letI : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
    Fintype.ofInjective (fun l ↦ l.idxFun) fun _ _ h ↦ Combinatorics.Line.ext h
  obtain ⟨V, hV⟩ | ⟨V, hV, hlines⟩ :=
    exists_subspace_many_lines hk hDHJ m hm δ hδ₀ hδ₁ n hn A hA
  · exact False.elim <| (not_lt_of_ge hV) (hsmall V)
  obtain ⟨C, hC, hCdense, hAC⟩ :=
    exists_endpoint_insensitive_intersection hk δ hδ₀ hm_large A V hfree hlines
  refine ⟨V, C, hC, hCdense, ?_⟩
  apply density_complement_bounds
  · exact hδ₀.le
  · exact (Parameters.η_pos hk hδ₀).le
  · simpa only [Subspace.relativeDensity, pullback] using hV
  · exact hCdense
  · exact hAC
  · exact Parameters.large_intersection_complement_gain hk hδ₀

/-- The part of the complement of an indexed intersection at which membership first fails. -/
def firstFailurePiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Finset X :=
  (C i)ᶜ ∩ Finset.univ.filter fun x ↦ ∀ j, j < i → x ∈ C j

/-- Replace the first failed set by its complement, retain the preceding sets, and make all
subsequent constraints vacuous. -/
def firstFailureFamily {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Fin k → Finset X :=
  fun j ↦ if j < i then C j else if j = i then (C j)ᶜ else Finset.univ

/-- **Hard helper:** the first-failure partition and its quantitative weighted averaging.

The complement of `intersection C` is partitioned by `firstFailurePiece C i`.  The two global
density estimates ensure that one piece is both large enough and has the required relative
`A`-density. -/
lemma exists_dense_firstFailurePiece {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (hC : Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ))
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  sorry

/-- **Hard helper:** the Boolean reconstruction of a first-failure piece as an insensitive
intersection.

Complement closure preserves the sensitivity pair at the failure index, while the universal
sets after that index impose no constraints. -/
lemma firstFailureFamily_facts {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    (∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j)) ∧
      IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i ∧
      Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint fun j ↦
        (firstFailurePiece C j : Set (ι → Fin (k + 1))) := by
  sorry

/-- Correlation with a positive-density intersection of insensitive families. -/
lemma exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (D i)) ∧
        Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ) ∧
        (δ + Parameters.γ k δ) * ((IsInsensitive.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ) := by
  classical
  by_cases hlarge : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)
  · obtain ⟨V, hV⟩ := hlarge
    letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    letI : DecidableEq (Fin m → Fin (k + 1)) := Classical.decEq _
    let D := fun _ : Fin k ↦ (Finset.univ : Finset (Fin m → Fin (k + 1)))
    have hD : IsInsensitive.intersection D = Finset.univ := by
      simpa only [IsInsensitive.intersection, D] using
        (Finset.inf_const (s := (Finset.univ : Finset (Fin k))) Finset.univ_nonempty
          (Finset.univ : Finset (Fin m → Fin (k + 1))))
    refine ⟨V, D, ?_, ?_, ?_⟩
    · intro i x y _
      simp only [D, Finset.mem_univ]
    · rw [hD]
      norm_num
      nlinarith [Parameters.η_le_δ_div_six k δ,
        Parameters.γ_le_η_sq_div_two k δ, Parameters.η_pos hk hδ₀,
        sq_nonneg (1 - Parameters.η k δ)]
    · rw [hD]
      norm_num
      change δ + Parameters.γ k δ ≤ (Subspace.relativeDensity V A : ℝ)
      linarith [Parameters.γ_le_η_sq_div_two k δ]
  · have hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        (Subspace.relativeDensity V A : ℝ) <
          δ + Parameters.η k δ ^ 2 / 2 := by
      intro V
      exact lt_of_not_ge fun hV ↦ hlarge ⟨V, hV⟩
    obtain ⟨V, C, hC, hCdense, hweighted, houtside⟩ :=
      exists_large_insensitive_intersection hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hn A hA
        hfree hsmall
    obtain ⟨i, hidense, hicorrelation⟩ :=
      exists_dense_firstFailurePiece hk hδ₀ hδ₁ (pullback V A) C hCdense hweighted
        houtside
    obtain ⟨hD, hintersection, _, _⟩ := firstFailureFamily_facts C hC i
    refine ⟨V, firstFailureFamily C i, hD, ?_, ?_⟩
    · rw [hintersection]
      exact hidense
    · rw [hintersection]
      exact hicorrelation

/-- A sufficient ambient dimension for the density-increment dichotomy. -/
opaque incrementBound (k d : ℕ) (δ : ℝ) : ℕ

/-- A dense word family either contains a line or has increased density on a prescribed-dimensional
subspace. -/
lemma density_increment {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : incrementBound k d δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  sorry

end DensityHalesJewett

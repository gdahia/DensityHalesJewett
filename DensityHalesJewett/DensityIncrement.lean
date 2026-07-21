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
  sorry

/-- A bound for the many-lines lemma. -/
opaque manyLinesBound (k m : ℕ) (δ : ℝ) : ℕ

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
lemma exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))]
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
  sorry

/-- A parameter-cube dimension sufficient for the insensitive-intersection construction. -/
opaque insensitiveIntersectionDimension (k : ℕ) (δ : ℝ) : ℕ

/-- A large intersection of insensitive families with a density gain on its complement. -/
lemma exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
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
  sorry

/-- Correlation with a positive-density intersection of insensitive families. -/
lemma exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
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
  sorry

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

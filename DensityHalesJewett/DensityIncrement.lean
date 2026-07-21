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

/-- The numerical parameters used in one density-increment step. -/
structure Data where
  /-- Dimension used for the auxiliary subspace. -/
  m₀ : ℕ
  /-- Density threshold for correlated fibers. -/
  θ : ℝ
  /-- Error tolerance in the density estimates. -/
  η : ℝ
  /-- Guaranteed density increment. -/
  γ : ℝ
  deriving Inhabited

/-- A positive dimension selected from the density Hales--Jewett assertion when available. -/
noncomputable def dimension (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.succ <| Nat.find <| h.2 (δ / 4) (by linarith)
  else 1

theorem dimension_pos (k : ℕ) (δ : ℝ) : 0 < dimension k δ := by
  classical
  unfold dimension
  split <;> simp

/-- The selected dimension is antitone in the density threshold. -/
theorem dimension_antitone {k : ℕ} (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : dimension k ρ ≤ dimension k δ := by
  classical
  rw [dimension, dif_pos ⟨hδ.trans_le hδρ, hDHJ⟩, dimension, dif_pos ⟨hδ, hDHJ⟩]
  apply Nat.succ_le_succ
  apply Nat.find_min'
  intro n hn A hA
  refine Nat.find_spec (hDHJ (δ / 4) (by linarith)) n hn A (le_trans (by gcongr) hA)

/-- The denominator in the parameter definition grows with the selected dimension. -/
theorem power_difference_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
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

/-- The denominator defining `theta` is positive for every admissible alphabet and density. -/
theorem denominator_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (_hδ : 0 < δ) :
    0 < ((k + 1 : ℕ) : ℝ) ^ dimension k δ - (k : ℝ) ^ dimension k δ := by
  apply sub_pos.mpr
  apply pow_lt_pow_left₀
  · exact_mod_cast Nat.lt_succ_self k
  · positivity
  · exact Nat.ne_of_gt <| dimension_pos k δ

/-- The correlated-fibers threshold attached to an alphabet size and density. -/
noncomputable def theta (k : ℕ) (δ : ℝ) : ℝ :=
  (δ / 4) /
    (((k + 1 : ℕ) : ℝ) ^ dimension k δ - (k : ℝ) ^ dimension k δ)

/-- The threshold is monotone in the density parameter. -/
theorem theta_mono {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : theta k δ ≤ theta k ρ := by
  unfold theta
  refine div_le_div₀ ?_ (by linarith) (denominator_pos hk (hδ.trans_le hδρ)) ?_
  · exact div_nonneg (hδ.trans_le hδρ).le (by norm_num)
  · exact power_difference_mono k <| dimension_antitone hDHJ hδ hδρ

/-- The threshold is monotone even when the density Hales--Jewett assertion is unavailable. -/
theorem theta_mono' {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : theta k δ ≤ theta k ρ := by
  classical
  by_cases hDHJ : HasDensityHJ k
  · exact theta_mono hk hDHJ hδ hδρ
  · unfold theta
    rw [dimension, dif_neg (fun h ↦ hDHJ h.2), dimension, dif_neg (fun h ↦ hDHJ h.2)]
    apply div_le_div_of_nonneg_right
    · linarith
    · rw [pow_one, pow_one, Nat.cast_add, Nat.cast_one]
      linarith

theorem theta_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < theta k δ := by
  unfold theta
  exact div_pos (by positivity) (denominator_pos hk hδ)

/-- The error tolerance attached to a threshold. -/
noncomputable def eta (δ θ : ℝ) : ℝ :=
  min (δ * θ / 48) (min (θ / 4) (δ / 6))

/-- The error tolerance is monotone in its density and threshold arguments. -/
theorem eta_mono {δ ρ θ τ : ℝ} (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hδρ : δ ≤ ρ) (hθτ : θ ≤ τ) : eta δ θ ≤ eta ρ τ := by
  unfold eta
  gcongr
  exact hδ.trans hδρ

theorem eta_pos {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) : 0 < eta δ θ := by
  unfold eta
  positivity

/-- The density increment attached to an error tolerance. -/
noncomputable def gamma (k : ℕ) (δ η : ℝ) : ℝ :=
  min (δ * η ^ 2 / k) (min (η ^ 2 / 2) (3 * η))

/-- The increment is monotone in its density and error-tolerance arguments. -/
theorem gamma_mono (k : ℕ) {δ ρ η ζ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hδρ : δ ≤ ρ) (hηζ : η ≤ ζ) : gamma k δ η ≤ gamma k ρ ζ := by
  unfold gamma
  gcongr
  exact hδ.trans hδρ

theorem gamma_pos {k : ℕ} (hk : 2 ≤ k) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    0 < gamma k δ η := by
  unfold gamma
  positivity

/-- Parameters attached to an alphabet size and density. -/
noncomputable def get (k : ℕ) (δ : ℝ) : Data :=
  let m₀ := dimension k δ
  ⟨m₀, theta k δ, eta δ (theta k δ), gamma k δ (eta δ (theta k δ))⟩

/-- Positivity and the elementary inequalities needed in the increment argument. -/
theorem facts {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₀ : 0 < δ) (_hδ₁ : δ ≤ 1) :
    0 < (get k δ).θ ∧
    0 < (get k δ).η ∧
    0 < (get k δ).γ ∧
    (get k δ).η < (get k δ).θ / 2 ∧
    (get k δ).η ≤ δ / 6 ∧
    (get k δ).γ ≤ (get k δ).η ^ 2 / 2 ∧
    (get k δ).γ ≤ 3 * (get k δ).η := by
  change 0 < theta k δ ∧ 0 < eta δ (theta k δ) ∧
    0 < gamma k δ (eta δ (theta k δ)) ∧
    eta δ (theta k δ) < theta k δ / 2 ∧
    eta δ (theta k δ) ≤ δ / 6 ∧
    gamma k δ (eta δ (theta k δ)) ≤ eta δ (theta k δ) ^ 2 / 2 ∧
    gamma k δ (eta δ (theta k δ)) ≤ 3 * eta δ (theta k δ)
  have hθ : 0 < theta k δ := theta_pos hk hδ₀
  have hη : 0 < eta δ (theta k δ) := eta_pos hδ₀ hθ
  refine ⟨hθ, hη, gamma_pos hk hδ₀ hη, ?_, ?_, ?_, ?_⟩
  · unfold eta
    refine lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) ?_
    linarith
  · unfold eta
    exact (min_le_right _ _).trans (min_le_right _ _)
  · unfold gamma
    exact (min_le_right _ _).trans (min_le_left _ _)
  · unfold gamma
    exact (min_le_right _ _).trans (min_le_right _ _)

/-- A density-independent positive lower bound for the increment above a fixed density floor. -/
noncomputable def gammaLowerBound (k : ℕ) (δ₀ : ℝ) : ℝ :=
  gamma k δ₀ (eta δ₀ (theta k δ₀))

/-- The increment parameters can be chosen uniformly above a fixed positive density floor. -/
theorem gamma_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < gammaLowerBound k δ₀ ∧
      ∀ ρ, δ₀ ≤ ρ → ρ ≤ 1 → gammaLowerBound k δ₀ ≤ (get k ρ).γ := by
  have hθ : 0 < theta k δ₀ := theta_pos hk hδ₀
  have hη : 0 < eta δ₀ (theta k δ₀) := eta_pos hδ₀ hθ
  refine ⟨gamma_pos hk hδ₀ hη, ?_⟩
  intro ρ hδρ _
  change gamma k δ₀ (eta δ₀ (theta k δ₀)) ≤ gamma k ρ (eta ρ (theta k ρ))
  refine gamma_mono k hδ₀.le hη.le hδρ ?_
  exact eta_mono hδ₀.le hθ.le hδρ (theta_mono' hk hδ₀ hδρ)

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
theorem exists_subspace_correlated_fibers {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hι : correlatedFibersBound k m δ ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - (Parameters.get k δ).η ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        (Parameters.get k δ).θ ≤
          ((Finset.univ.filter fun y ↦ ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  sorry

/-- A bound for the many-lines lemma. -/
opaque manyLinesBound (k m : ℕ) (δ : ℝ) : ℕ

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
theorem exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + (Parameters.get k δ).η ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * (Parameters.get k δ).η ≤ (Subspace.relativeDensity V A : ℝ) ∧
      (Parameters.get k δ).θ / 2 ≤
        ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  sorry

/-- A parameter-cube dimension sufficient for the insensitive-intersection construction. -/
opaque insensitiveIntersectionDimension (k : ℕ) (δ : ℝ) : ℕ

/-- A large intersection of insensitive families with a density gain on its complement. -/
theorem exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A)
    (hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (Subspace.relativeDensity V A : ℝ) < δ + (Parameters.get k δ).η ^ 2 / 2) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
        (Parameters.get k δ).θ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
        (δ + 6 * (Parameters.get k δ).η) *
            ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
        δ - 3 * (Parameters.get k δ).η ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  sorry

/-- Correlation with a positive-density intersection of insensitive families. -/
theorem exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (D i)) ∧
        (Parameters.get k δ).γ ≤ ((IsInsensitive.intersection D).dens : ℝ) ∧
        (δ + (Parameters.get k δ).γ) * ((IsInsensitive.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ) := by
  sorry

/-- A sufficient ambient dimension for the density-increment dichotomy. -/
opaque incrementBound (k d : ℕ) (δ : ℝ) : ℕ

/-- A dense word family either contains a line or has increased density on a prescribed-dimensional
subspace. -/
theorem density_increment {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : incrementBound k d δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        δ + (Parameters.get k δ).γ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  sorry

end DensityHalesJewett

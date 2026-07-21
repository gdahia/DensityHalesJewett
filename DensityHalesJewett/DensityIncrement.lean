/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Insensitive

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
  m₀ : ℕ
  θ : ℝ
  η : ℝ
  γ : ℝ
  deriving Inhabited

/-- Parameters attached to an alphabet size and density. -/
opaque get (k : ℕ) (δ : ℝ) : Data

/-- Positivity and the elementary inequalities needed in the increment argument. -/
theorem facts {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
    0 < (get k δ).θ ∧
    0 < (get k δ).η ∧
    0 < (get k δ).γ ∧
    (get k δ).η < (get k δ).θ / 2 ∧
    (get k δ).η ≤ δ / 6 ∧
    (get k δ).γ ≤ (get k δ).η ^ 2 / 2 ∧
    (get k δ).γ ≤ 3 * (get k δ).η := by
  sorry

/-- A density-independent positive lower bound for the increment above a fixed density floor. -/
opaque gammaLowerBound (k : ℕ) (δ₀ : ℝ) : ℝ

/-- The increment parameters can be chosen uniformly above a fixed positive density floor. -/
theorem gamma_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < gammaLowerBound k δ₀ ∧
      ∀ ρ, δ₀ ≤ ρ → ρ ≤ 1 → gammaLowerBound k δ₀ ≤ (get k ρ).γ := by
  sorry

end Parameters

/-- A finite word family contains no complete combinatorial line. -/
def IsLineFree {α ι : Type*} [DecidableEq (ι → α)] (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A

/-- Pull a word family back to the parameter cube of a subspace. -/
def pullback {η α ι : Type*} [Fintype (η → α)] [DecidableEq (η → α)]
    [DecidableEq (ι → α)] (V : Combinatorics.Subspace η α ι)
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
    [DecidableEq (κ → Fin (k + 1))] [DecidableEq (ι ⊕ κ → Fin (k + 1))]
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

/-- A large intersection of insensitive families with a density gain on its complement. -/
theorem exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
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

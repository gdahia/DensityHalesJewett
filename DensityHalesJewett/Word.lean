/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Real.Basic

/-!
# Finite word spaces

Uniform density, concatenation of words, fibers, and elementary averaging results used in the
density Hales--Jewett argument.  We use `Finset.dens` for uniform density and
`Equiv.sumArrowEquivProdArrow` for the underlying decomposition of a word on a sum of coordinate
types.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHalesJewett

/-- Concatenate words on disjoint coordinate types. -/
def concat {α ι κ : Type*} (x : ι → α) (y : κ → α) : ι ⊕ κ → α :=
  (Equiv.sumArrowEquivProdArrow ι κ α).symm (x, y)

@[simp]
theorem concat_apply_inl {α ι κ : Type*} (x : ι → α) (y : κ → α) (i : ι) :
    concat x y (Sum.inl i) = x i := by
  rfl

@[simp]
theorem concat_apply_inr {α ι κ : Type*} (x : ι → α) (y : κ → α) (i : κ) :
    concat x y (Sum.inr i) = y i := by
  rfl

/-- The fiber of a word family above a fixed prefix. -/
def fiber {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) :=
  Finset.univ.filter fun y ↦ concat x y ∈ A

@[simp]
theorem mem_fiber {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (κ → α)]
    [DecidableEq (ι ⊕ κ → α)]
    {A : Finset (ι ⊕ κ → α)} {x : ι → α} {y : κ → α} :
    y ∈ fiber A x ↔ concat x y ∈ A := by
  simp [fiber]

/-- Uniform density is the average of the uniform densities of the fibers. -/
theorem average_density_fiber {α ι κ : Type*} [Fintype (ι → α)] [Fintype (κ → α)]
    [Fintype (ι ⊕ κ → α)] [DecidableEq (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) :
    (𝔼 x : ι → α, ((fiber A x).dens : ℝ)) = (A.dens : ℝ) := by
  sorry

/-- A bounded function with large average exceeds a lower threshold on a quantitatively large
set. -/
theorem density_ge_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (a b : ℝ) (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1)
    (hb : 0 ≤ b) (hba : b < a) (havg : a ≤ 𝔼 x : X, f x) :
    (a - b) / (1 - b) ≤
      ((Finset.univ.filter fun x ↦ b ≤ f x).dens : ℝ) := by
  sorry

end DensityHalesJewett

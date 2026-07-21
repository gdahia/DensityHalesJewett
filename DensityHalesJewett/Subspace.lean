/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Word

/-!
# Combinatorial subspaces

Ranges, containment, relative density, alphabet restriction, and lines inside mathlib's
`Combinatorics.Subspace`.
-/

@[expose] public section

open Finset Function
open Combinatorics

namespace DensityHalesJewett
namespace Subspace

variable {η α ι : Type*}

/-- Evaluation by a fixed combinatorial subspace is injective when the alphabet is nontrivial. -/
theorem injective [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
    Function.Injective V := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  simpa only [V.apply_inr hi] using congrFun hxy i

/-- The finite range of a combinatorial subspace. -/
def range [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) : Finset (ι → α) :=
  Finset.univ.image V

@[simp]
theorem mem_range [Fintype (η → α)] [DecidableEq (ι → α)]
    {V : Combinatorics.Subspace η α ι} {w : ι → α} :
    w ∈ range V ↔ ∃ x, V x = w := by
  simp [range]

/-- A subspace is contained in a finite word family when all its evaluations belong to it. -/
def IsContained (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Prop :=
  ∀ x, V x ∈ A

/-- Relative density on a subspace, defined on its parameter cube. -/
def relativeDensity [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℚ≥0 :=
  (Finset.univ.filter fun x ↦ V x ∈ A).dens

/-- Ambient line structures whose evaluations are contained in a subspace. -/
def Lines [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) :=
  {l : Combinatorics.Line α ι // ∀ a, l a ∈ range V}

/-- Composition with a subspace identifies parameter-cube lines with ambient lines contained in
the subspace. -/
noncomputable def linesEquiv [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
    Combinatorics.Line α η ≃ Lines V := by
  sorry

/-- Map a parameter-cube line to the corresponding ambient line in a subspace. -/
noncomputable def mapLine [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι :=
  (linesEquiv V l).1

/-- Restrict the variable letters of a subspace along an alphabet embedding. -/
def restrictAlphabet {β : Type*} [Fintype (η → β)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (e : β ↪ α) : Finset (ι → α) :=
  Finset.univ.image fun x ↦ V (e ∘ x)

end Subspace
end DensityHalesJewett

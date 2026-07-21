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
lemma injective [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
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
lemma mem_range [Fintype (η → α)] [DecidableEq (ι → α)]
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

/-- Compose a parameter-cube line with a combinatorial subspace. -/
def composeLine (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := V.proper e
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, he]

@[simp]
lemma composeLine_apply (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : composeLine V l a = V (l a) := by
  funext i
  cases hi : V.idxFun i
  · simp [composeLine, Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply, hi]
  · simp [composeLine, Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply, hi]

/-- Regard the composite of a parameter line with a subspace as a line in that subspace. -/
def composeLineToLines [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) : Lines V :=
  ⟨composeLine V l, fun a ↦ mem_range.mpr ⟨l a, (composeLine_apply V l a).symm⟩⟩

/-- The canonical parameter word representing a point of a line contained in a subspace. -/
noncomputable def parameterWord [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) : η → α :=
  Classical.choose <| mem_range.mp (q.2 a)

lemma parameterWord_apply [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) :
    V (parameterWord V q a) = q.1 a :=
  Classical.choose_spec <| mem_range.mp (q.2 a)

/-- A chosen coordinate on which a subspace realizes a given parameter direction. -/
noncomputable def properCoordinate (V : Combinatorics.Subspace η α ι) (e : η) : ι :=
  Classical.choose <| V.proper e

lemma properCoordinate_spec (V : Combinatorics.Subspace η α ι) (e : η) :
    V.idxFun (properCoordinate V e) = Sum.inr e :=
  Classical.choose_spec <| V.proper e

/-- Recover the parameter-cube line underlying an ambient line contained in a subspace. -/
noncomputable def uncomposeLine [Fintype (η → α)] [DecidableEq (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) : Combinatorics.Line α η where
  idxFun e := q.1.idxFun (properCoordinate V e)
  proper := by
    obtain ⟨j, hj⟩ := q.1.proper
    cases hVj : V.idxFun j with
    | inl b =>
      obtain ⟨a, hab⟩ := exists_ne b
      exfalso
      apply hab
      rw [← q.1.apply_none a j hj, ← parameterWord_apply V q a]
      exact V.apply_inl hVj
    | inr e =>
      cases hq : q.1.idxFun (properCoordinate V e) with
      | none => exact ⟨e, hq⟩
      | some c =>
        obtain ⟨a, hac⟩ := exists_ne c
        exfalso
        apply hac
        rw [← q.1.apply_none a j hj, ← q.1.apply_some hq]
        rw [← parameterWord_apply V q a]
        rw [V.apply_inr (properCoordinate_spec V e), V.apply_inr hVj]

lemma uncomposeLine_apply [Fintype (η → α)] [DecidableEq (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) :
    V (uncomposeLine V q a) = q.1 a := by
  funext i
  cases hi : V.idxFun i with
  | inl b =>
    rw [V.apply_inl hi]
    rw [← parameterWord_apply V q a]
    rw [V.apply_inl hi]
  | inr e =>
    rw [V.apply_inr hi]
    change (q.1.idxFun (properCoordinate V e)).getD a = q.1 a i
    change q.1 a (properCoordinate V e) = q.1 a i
    rw [← parameterWord_apply V q a]
    rw [V.apply_inr (properCoordinate_spec V e), V.apply_inr hi]

/-- Composition with a subspace identifies parameter-cube lines with ambient lines contained in
the subspace. -/
noncomputable def linesEquiv [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
    Combinatorics.Line α η ≃ Lines V := by
  refine
    { toFun := composeLineToLines V
      invFun := uncomposeLine V
      left_inv := ?_
      right_inv := ?_ }
  · intro l
    apply Combinatorics.Line.coe_injective
    funext a
    apply injective V
    rw [uncomposeLine_apply]
    exact composeLine_apply V l a
  · intro q
    apply Subtype.ext
    change composeLine V (uncomposeLine V q) = q.1
    apply Combinatorics.Line.coe_injective
    funext a
    rw [composeLine_apply]
    exact uncomposeLine_apply V q a

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

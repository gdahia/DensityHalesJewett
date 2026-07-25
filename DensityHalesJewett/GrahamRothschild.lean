/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Subspace
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Graham--Rothschild theorem for combinatorial lines

The finite-unions focusing argument, block canonization, and the line-coloring form of the
Graham--Rothschild theorem needed by the density proof.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

namespace FiniteUnions

/-- A Hales--Jewett dimension sufficient to focus `q` color profiles simultaneously. -/
lemma exists_focus_dimension (alphabet colors q : ℕ) (halphabet : 0 < alphabet) :
    ∃ N, ∀ n ≥ N, ∀ χ : (Fin n → Fin alphabet) → Fin q → Fin colors,
      ∃ l : Combinatorics.Line (Fin alphabet) (Fin n), ∃ c, ∀ a, χ (l a) = c := by
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension
    (Fin alphabet) (Fin q → Fin colors)
  let e := Fintype.equivFin ι
  let N := Fintype.card ι
  refine ⟨N, ?_⟩
  intro n hn
  rw [← Nat.add_sub_of_le hn]
  intro χ
  let x₀ : Fin alphabet := ⟨0, halphabet⟩
  obtain ⟨l, c, hc⟩ := hι fun w i ↦
    χ (Fin.addCases (fun j ↦ w (e.symm j)) (fun _ ↦ x₀)) i
  let l' : Combinatorics.Line (Fin alphabet) (Fin (N + (n - N))) :=
    { idxFun := Fin.addCases (fun i ↦ l.idxFun (e.symm i)) (fun _ ↦ some x₀)
      proper := by
        obtain ⟨i, hi⟩ := l.proper
        refine ⟨Fin.castAdd (n - N) (e i), ?_⟩
        simp only [Fin.addCases_left, e, Equiv.symm_apply_apply, hi] }
  refine ⟨l', c, ?_⟩
  intro a
  funext i
  convert congrFun (hc a) i using 1
  apply congrArg (fun w ↦ χ w i)
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [l', Combinatorics.Line.coe_apply, Fin.addCases_left]
  · intro i
    simp only [l', Combinatorics.Line.coe_apply, Fin.addCases_right, Option.getD_some]

/-- A Hales--Jewett dimension sufficient to focus `q` color profiles simultaneously. -/
noncomputable def focusBound (alphabet colors q : ℕ) : ℕ :=
  by
    classical
    exact if halphabet : 0 < alphabet then
      Nat.find (exists_focus_dimension alphabet colors q halphabet)
    else 0

lemma focusBound_spec (alphabet colors q n : ℕ) (halphabet : 0 < alphabet)
    (hn : focusBound alphabet colors q ≤ n) :
    ∀ χ : (Fin n → Fin alphabet) → Fin q → Fin colors,
      ∃ l : Combinatorics.Line (Fin alphabet) (Fin n), ∃ c, ∀ a, χ (l a) = c := by
  classical
  rw [focusBound, dif_pos halphabet] at hn
  exact (Nat.find_spec (exists_focus_dimension alphabet colors q halphabet)) n hn

/-- The simultaneous color-profile focusing step used in the finite-unions argument. -/
lemma focus (A C U : Type*) [Fintype A] [Nonempty A] [Fintype C] [Fintype U]
    (n : ℕ) (hn : focusBound (Fintype.card A) (Fintype.card C) (Fintype.card U) ≤ n)
    (χ : U → (Fin n → A) → C) :
    ∃ l : Combinatorics.Line A (Fin n), ∀ u, ∃ c, ∀ a, χ u (l a) = c := by
  let eA := Fintype.equivFin A
  let eC := Fintype.equivFin C
  let eU := Fintype.equivFin U
  obtain ⟨l, c, hc⟩ := focusBound_spec (Fintype.card A) (Fintype.card C) (Fintype.card U) n
    (Fintype.card_pos_iff.mpr inferInstance) hn fun w u ↦
      eC (χ (eU.symm u) (eA.symm ∘ w))
  refine ⟨l.map eA.symm, ?_⟩
  intro u
  refine ⟨eC.symm (c (eU u)), ?_⟩
  intro a
  apply eC.injective
  rw [← eA.symm_apply_apply a, Combinatorics.Line.map_apply]
  simpa only [eA, eC, eU, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    Function.comp_apply] using congrFun (hc (eA a)) (eU u)

/-- In the finite cardinal color model, iterated focusing produces ordered blocks whose union
color is determined by the first selected block. -/
private lemma exists_minColor_blocks_fin (colors s : ℕ) :
    ∃ L, ∀ χ : Finset (Fin L) → Fin colors,
      ∃ B : Fin s → Finset (Fin L),
        (∀ i, (B i).Nonempty) ∧
        (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
        ∃ κ : Fin s → Fin colors, ∀ I : Finset (Fin s), (hI : I.Nonempty) →
          χ (I.biUnion B) = κ (I.min' hI) := by
  sorry

/-- The finite-cardinal min-color block theorem transports along an equivalence of color
types. -/
private lemma exists_minColor_blocks_of_fin (C : Type*) [Fintype C] (s : ℕ)
    (hfin :
      ∃ L, ∀ χ : Finset (Fin L) → Fin (Fintype.card C),
        ∃ B : Fin s → Finset (Fin L),
          (∀ i, (B i).Nonempty) ∧
          (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
          ∃ κ : Fin s → Fin (Fintype.card C),
            ∀ I : Finset (Fin s), (hI : I.Nonempty) →
              χ (I.biUnion B) = κ (I.min' hI)) :
    ∃ L, ∀ χ : Finset (Fin L) → C,
      ∃ B : Fin s → Finset (Fin L),
        (∀ i, (B i).Nonempty) ∧
        (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
        ∃ κ : Fin s → C, ∀ I : Finset (Fin s), (hI : I.Nonempty) →
          χ (I.biUnion B) = κ (I.min' hI) := by
  sorry

/-- Iterated colored Hales--Jewett focusing produces an ordered block sequence whose union color
is determined by the first selected block.

At each stage, split the unused final interval into equal consecutive packets.  A word records one
of the finitely many allowed choices in every packet, and its color is the complete profile over
all unions of the blocks already selected.  `focus` supplies a monochromatic line for this profile.
The variable packets form the next block; the fixed packets are absorbed into the stem carried by
the induction.  Iterating from right to left preserves the order of the blocks. -/
private lemma exists_minColor_blocks (C : Type*) [Finite C] (s : ℕ) :
    ∃ L, ∀ χ : Finset (Fin L) → C,
      ∃ B : Fin s → Finset (Fin L),
        (∀ i, (B i).Nonempty) ∧
        (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
        ∃ κ : Fin s → C, ∀ I : Finset (Fin s), (hI : I.Nonempty) →
          χ (I.biUnion B) = κ (I.min' hI) := by
  letI := Fintype.ofFinite C
  exact exists_minColor_blocks_of_fin C s <|
    exists_minColor_blocks_fin (Fintype.card C) s

/-- The finite-unions theorem in ordered block-sequence form.

Apply `exists_minColor_blocks` with more than `m - 1` indices of each possible color.  The finite
pigeonhole principle gives `m` indices on which `κ` is constant.  Reindexing the corresponding
blocks in increasing order preserves the block condition, and every nonempty union has the color
of its least selected index, hence has that common color. -/
lemma exists_mono (C : Type*) [Finite C] (m : ℕ) :
    ∃ L, ∀ χ : Finset (Fin L) → C,
      ∃ B : Fin m → Finset (Fin L),
        (∀ i, (B i).Nonempty) ∧
        (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
        ∃ c, ∀ I : Finset (Fin m), I.Nonempty → χ (I.biUnion B) = c := by
  classical
  cases isEmpty_or_nonempty C with
  | inl hC =>
      letI : IsEmpty C := hC
      refine ⟨0, ?_⟩
      intro χ
      exact isEmptyElim (χ ∅)
  | inr hC =>
      letI : Nonempty C := hC
      letI := Fintype.ofFinite C
      let s := Fintype.card C * m
      obtain ⟨L, hL⟩ := exists_minColor_blocks C s
      refine ⟨L, ?_⟩
      intro χ
      obtain ⟨B, hBne, hBorder, κ, hκ⟩ := hL χ
      obtain ⟨c, hc⟩ :=
        Fintype.exists_le_card_fiber_of_mul_le_card (f := κ) (n := m) (by simp [s])
      let fiber := Finset.univ.filter fun i ↦ κ i = c
      obtain ⟨J, hJfiber, hJcard⟩ :=
        Finset.exists_subset_card_eq (s := fiber) (n := m) (by simpa only [fiber] using hc)
      let e : Fin m ↪o Fin s := J.orderEmbOfFin hJcard
      let B' : Fin m → Finset (Fin L) := fun i ↦ B (e i)
      refine ⟨B', ?_, ?_, c, ?_⟩
      · intro i
        exact hBne (e i)
      · intro i j hij x hx y hy
        exact hBorder (e i) (e j) (e.strictMono hij) x hx y hy
      · intro I hI
        let I' := I.map e.toEmbedding
        have hI' : I'.Nonempty := hI.map
        rw [show I.biUnion B' = I'.biUnion B by
          ext x
          simp only [B', I', Finset.mem_biUnion, Finset.mem_map]
          constructor
          · rintro ⟨i, hi, hx⟩
            exact ⟨e i, ⟨i, hi, rfl⟩, hx⟩
          · rintro ⟨_, ⟨i, hi, rfl⟩, hx⟩
            exact ⟨i, hi, hx⟩]
        rw [hκ I' hI']
        have hminJ : I'.min' hI' ∈ J := by
          obtain ⟨i, _, hi⟩ := Finset.mem_map.mp (I'.min'_mem hI')
          rw [← hi]
          exact J.orderEmbOfFin_mem hJcard i
        simpa only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] using hJfiber hminJ

/-- The finite-unions theorem remains valid after adding unused final coordinates. -/
lemma exists_mono_in_high_dimension (C : Type*) [Finite C] (m : ℕ) :
    ∃ L, ∀ n ≥ L, ∀ χ : Finset (Fin n) → C,
      ∃ B : Fin m → Finset (Fin n),
        (∀ i, (B i).Nonempty) ∧
        (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
        ∃ c, ∀ I : Finset (Fin m), I.Nonempty → χ (I.biUnion B) = c := by
  classical
  obtain ⟨L, hL⟩ := exists_mono C m
  refine ⟨L, ?_⟩
  intro n hn χ
  let e : Fin L ↪ Fin n :=
    { toFun := fun i ↦ ⟨i, i.isLt.trans_le hn⟩
      inj' := fun i j hij ↦ Fin.ext <| congrArg (fun x : Fin n ↦ x.val) hij }
  obtain ⟨B, hBne, hBorder, c, hBc⟩ := hL fun s ↦ χ (s.map e)
  refine ⟨fun i ↦ (B i).map e, ?_, ?_, c, ?_⟩
  · intro i
    exact (hBne i).map
  · intro i j hij x hx y hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact hBorder i j hij x' hx' y' hy'
  · intro I hI
    rw [← hBc I hI]
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_map]
    constructor
    · rintro ⟨i, hi, y, hy, hyx⟩
      exact ⟨y, ⟨i, hi, hy⟩, hyx⟩
    · rintro ⟨y, ⟨i, hi, hy⟩, hyx⟩
      exact ⟨i, hi, y, hy, hyx⟩

/-- A dimension sufficient for the finite-unions theorem. -/
noncomputable def bound (colors m : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_mono_in_high_dimension (Fin colors) m)

lemma bound_spec (C : Type*) [Fintype C] (m n : ℕ)
    (hn : bound (Fintype.card C) m ≤ n) (χ : Finset (Fin n) → C) :
    ∃ B : Fin m → Finset (Fin n),
      (∀ i, (B i).Nonempty) ∧
      (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
      ∃ c, ∀ I : Finset (Fin m), I.Nonempty → χ (I.biUnion B) = c := by
  classical
  let eC := Fintype.equivFin C
  obtain ⟨B, hBne, hBorder, c, hBc⟩ :=
    (Nat.find_spec (exists_mono_in_high_dimension (Fin (Fintype.card C)) m)) n hn
      fun s ↦ eC (χ s)
  refine ⟨B, hBne, hBorder, eC.symm c, ?_⟩
  intro I hI
  apply eC.injective
  simpa only [Equiv.apply_symm_apply] using hBc I hI

end FiniteUnions

namespace GrahamRothschild

/-- The variable coordinates of a combinatorial line. -/
def variableSet {α ι : Type*} [Fintype ι] (l : Combinatorics.Line α ι) : Finset ι :=
  Finset.univ.filter fun i ↦ l.idxFun i = none

/-- A subspace is locally canonizing when changing the fixed letter at one parameter coordinate
does not change the color, provided the variable support is unchanged. -/
def IsLocallyCanonizing {α C : Type*} [Fintype α] [Nontrivial α] [DecidableEq α] {L n : ℕ}
    (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (χ : Combinatorics.Line α (Fin n) → C) : Prop :=
  ∀ p q : Combinatorics.Line α (Fin L), variableSet p = variableSet q →
    (∃ i, ∀ j, j ≠ i → p.idxFun j = q.idxFun j) →
      χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q)

/-- Reverse finite focusing constructs a locally canonizing block subspace in one sufficiently
large exact dimension. -/
lemma exists_locally_canonizing_dimension (alphabet colors blocks : ℕ)
    [Nontrivial (Fin alphabet)] (halphabet : 2 ≤ alphabet) :
    ∃ N, ∀ χ : Combinatorics.Line (Fin alphabet) (Fin N) → Fin colors,
      ∃ V : Combinatorics.Subspace (Fin blocks) (Fin alphabet) (Fin N),
        IsLocallyCanonizing V χ := by
  sorry

/-- A locally canonizing block subspace remains available after padding with unused final
coordinates. -/
lemma exists_locally_canonizing_in_high_dimension (alphabet colors blocks : ℕ)
    [Nontrivial (Fin alphabet)] (halphabet : 2 ≤ alphabet) :
    ∃ N, ∀ n ≥ N, ∀ χ : Combinatorics.Line (Fin alphabet) (Fin n) → Fin colors,
      ∃ V : Combinatorics.Subspace (Fin blocks) (Fin alphabet) (Fin n),
        IsLocallyCanonizing V χ := by
  sorry

/-- A block-canonization dimension. -/
noncomputable def canonizationBound (alphabet colors blocks : ℕ) : ℕ := by
  classical
  exact if halphabet : 2 ≤ alphabet then
    letI : Nontrivial (Fin alphabet) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        simp only [Fintype.card_fin]
        omega)
    Nat.find (exists_locally_canonizing_in_high_dimension alphabet colors blocks halphabet)
  else 0

/-- The cardinal-model canonization threshold transports to arbitrary finite alphabets and color
types. -/
lemma canonizationBound_spec (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (L n : ℕ)
    (hn : canonizationBound (Fintype.card α) (Fintype.card C) L ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin L) α (Fin n),
      IsLocallyCanonizing V χ := by
  sorry

/-- Local one-coordinate color invariance extends to arbitrary fixed-letter changes with the same
variable support. -/
lemma color_eq_of_locally_canonizing (α C : Type*) [Fintype α] [Nontrivial α]
    [DecidableEq α] {L n : ℕ}
    (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (χ : Combinatorics.Line α (Fin n) → C)
    (hlocal : IsLocallyCanonizing V χ)
    (p q : Combinatorics.Line α (Fin L)) (hpq : variableSet p = variableSet q) :
    χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q) := by
  sorry

/-- Block canonization: inside a suitable subspace, the color of a line depends only on its
variable directions and not on its fixed letters. -/
lemma canonize (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (L n : ℕ)
    (hn : canonizationBound (Fintype.card α) (Fintype.card C) L ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin L) α (Fin n),
      ∀ p q : Combinatorics.Line α (Fin L), variableSet p = variableSet q →
        χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q) := by
  obtain ⟨V, hV⟩ := canonizationBound_spec α C L n hn χ
  refine ⟨V, ?_⟩
  intro p q hpq
  exact color_eq_of_locally_canonizing α C V χ hV p q hpq

/-- Finite unions applied to a canonized line coloring.

The coloring induced on nonempty variable supports is monochromatic on every nonempty union of
an ordered block sequence.  Constructing the induced support coloring requires handling the empty
support without assuming `C` is inhabited. -/
lemma color_nonempty_of_finiteUnions_bound (α C : Type*) [Nontrivial α]
    [Fintype C] (m L n : ℕ) (hm : 1 ≤ m)
    (hL : FiniteUnions.bound (Fintype.card C) m ≤ L)
    (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (χ : Combinatorics.Line α (Fin n) → C) : Nonempty C := by
  sorry

/-- Once the color type is inhabited, canonization turns the line coloring into a coloring of
nonempty variable supports, to which the finite-unions theorem applies. -/
lemma exists_canonized_finiteUnions_blocks_of_nonempty (α C : Type*) [Fintype α]
    [Nontrivial α] [Fintype C] [Nonempty C] [DecidableEq α] (m L n : ℕ)
    (hL : FiniteUnions.bound (Fintype.card C) m ≤ L)
    (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (χ : Combinatorics.Line α (Fin n) → C)
    (hχ : ∀ p q : Combinatorics.Line α (Fin L), variableSet p = variableSet q →
      χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q)) :
    ∃ B : Fin m → Finset (Fin L),
      (∀ i, (B i).Nonempty) ∧
      (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
      ∃ c, ∀ I : Finset (Fin m), I.Nonempty →
        ∀ p : Combinatorics.Line α (Fin L), variableSet p = I.biUnion B →
          χ (Subspace.mapLine V p) = c := by
  sorry

/-- Finite unions applied to a canonized line coloring.

The coloring induced on nonempty variable supports is monochromatic on every nonempty union of
an ordered block sequence.  Constructing the induced support coloring requires handling the empty
support without assuming `C` is inhabited. -/
lemma exists_canonized_finiteUnions_blocks (α C : Type*) [Fintype α] [Nontrivial α]
    [Fintype C] [DecidableEq α] (m L n : ℕ) (hm : 1 ≤ m)
    (hL : FiniteUnions.bound (Fintype.card C) m ≤ L)
    (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (χ : Combinatorics.Line α (Fin n) → C)
    (hχ : ∀ p q : Combinatorics.Line α (Fin L), variableSet p = variableSet q →
      χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q)) :
    ∃ B : Fin m → Finset (Fin L),
      (∀ i, (B i).Nonempty) ∧
      (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
      ∃ c, ∀ I : Finset (Fin m), I.Nonempty →
        ∀ p : Combinatorics.Line α (Fin L), variableSet p = I.biUnion B →
          χ (Subspace.mapLine V p) = c := by
  letI : Nonempty C :=
    color_nonempty_of_finiteUnions_bound α C m L n hm hL V χ
  exact exists_canonized_finiteUnions_blocks_of_nonempty α C m L n hL V χ hχ

/-- The variable support of a combinatorial line is nonempty. -/
lemma variableSet_nonempty {α : Type*} {m : ℕ} (l : Combinatorics.Line α (Fin m)) :
    (variableSet l).Nonempty := by
  dsimp only [variableSet]
  apply filter_nonempty_iff.mpr
  obtain ⟨a, ha⟩ := l.proper
  exact ⟨a, ⟨by simp, ha⟩⟩


/-- Ordered nonempty blocks determine a subspace whose parameter directions occur exactly on
their corresponding blocks. -/
lemma exists_subspace_indexed_by_ordered_blocks (α : Type*) [Nontrivial α]
    {m L : ℕ} (B : Fin m → Finset (Fin L))
    (hBne : ∀ i, (B i).Nonempty)
    (hBorder : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) :
    ∃ W : Combinatorics.Subspace (Fin m) α (Fin L),
      ∀ i j, W.idxFun i = Sum.inr j ↔ i ∈ B j := by
  sorry

/-- The variable support of a line mapped through a block-indexed subspace is the union of the
blocks indexed by the original variable support. -/
lemma variableSet_mapLine_of_indexed_blocks (α : Type*) [Fintype α] [Nontrivial α]
    [DecidableEq α] {m L : ℕ} (W : Combinatorics.Subspace (Fin m) α (Fin L))
    (B : Fin m → Finset (Fin L))
    (hW : ∀ i j, W.idxFun i = Sum.inr j ↔ i ∈ B j)
    (l : Combinatorics.Line α (Fin m)) :
    variableSet (Subspace.mapLine W l) = (variableSet l).biUnion B := by
  sorry

/-- Mapping a line through a composite subspace agrees with mapping it through the two subspaces
successively. -/
lemma mapLine_compose (α : Type*) [Fintype α] [Nontrivial α] [DecidableEq α]
    {m L n : ℕ} (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (W : Combinatorics.Subspace (Fin m) α (Fin L))
    (l : Combinatorics.Line α (Fin m)) :
    Subspace.mapLine (Subspace.compose V W) l =
      Subspace.mapLine V (Subspace.mapLine W l) := by
  sorry

/-- Assemble ordered finite-unions blocks into a subspace.

Every parameter line of the resulting subspace has variable support equal to the union of the
blocks indexed by its variable directions.  The final equality records compatibility of this
construction with mapping a line through a composite subspace. -/
lemma exists_ordered_block_subspace (α : Type*) [Fintype α] [Nontrivial α]
    [DecidableEq α] {m L n : ℕ} (V : Combinatorics.Subspace (Fin L) α (Fin n))
    (B : Fin m → Finset (Fin L)) (hBne : ∀ i, (B i).Nonempty)
    (hBorder : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) :
    ∃ W : Combinatorics.Subspace (Fin m) α (Fin L),
      ∀ l : Combinatorics.Line α (Fin m),
        ∃ I : Finset (Fin m), I.Nonempty ∧
          variableSet (Subspace.mapLine W l) = I.biUnion B ∧
          Subspace.mapLine (Subspace.compose V W) l =
            Subspace.mapLine V (Subspace.mapLine W l) := by
  obtain ⟨W, hW⟩ :=
    exists_subspace_indexed_by_ordered_blocks α B hBne hBorder
  refine ⟨W, ?_⟩
  intro l
  refine ⟨variableSet l, variableSet_nonempty l, ?_, ?_⟩
  · exact variableSet_mapLine_of_indexed_blocks α W B hW l
  · exact mapLine_compose α V W l

/-- A Graham--Rothschild dimension for colorings of combinatorial lines. -/
noncomputable def bound (alphabet colors dimension : ℕ) : ℕ :=
  canonizationBound alphabet colors (FiniteUnions.bound colors dimension)

/-- The line case of the Graham--Rothschild theorem. -/
lemma lines (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  let L := FiniteUnions.bound (Fintype.card C) m
  obtain ⟨V, hV⟩ := canonize α C L n (by simpa only [bound, L] using hn) χ
  obtain ⟨B, hBne, hBorder, c, hBc⟩ :=
    exists_canonized_finiteUnions_blocks α C m L n hm le_rfl V χ hV
  obtain ⟨W, hW⟩ := exists_ordered_block_subspace α V B hBne hBorder
  refine ⟨Subspace.compose V W, c, ?_⟩
  intro l
  obtain ⟨I, hI, hvariable, hmap⟩ := hW l
  rw [hmap]
  exact hBc I hI (Subspace.mapLine W l) hvariable

/-- The two-color form of Graham--Rothschild used by the density argument. -/
lemma lines_twoColor (α : Type*) [Fintype α] [Nontrivial α] [DecidableEq α]
    (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) 2 m ≤ n)
    (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∉ L) := by
  classical
  obtain ⟨V, c, hc⟩ :=
    lines α (Fin 2) m n hm hn fun l ↦ if l ∈ L then 0 else 1
  obtain rfl | ⟨c, rfl⟩ := c.eq_zero_or_eq_succ
  · refine ⟨V, Or.inl ?_⟩
    intro l
    by_contra h
    simpa [h] using hc l
  · refine ⟨V, Or.inr ?_⟩
    rw [Fin.eq_zero c] at hc
    intro l h
    simpa [h] using hc l

end GrahamRothschild
end DensityHalesJewett

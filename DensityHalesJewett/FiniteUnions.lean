/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort

/-!
# Finite unions of disjoint sets from the multidimensional Hales--Jewett theorem

For a colouring of the subsets of a large finite index set we produce pairwise disjoint nonempty
blocks all of whose nonempty unions receive the same colour.  The argument follows the finite
unions section of `graham_rothschild_lines_from_mhj.tex`: the multidimensional Hales--Jewett
theorem over the alphabet `Bool` gives a translated combinatorial cube of sets, iterating it
canonizes the colour of a union in terms of its least block, and the pigeonhole principle
extracts a monochromatic family.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett
namespace FiniteUnions

/-- A translated combinatorial cube of sets: a base block `E` and wildcard blocks `G` such that
every union of `E` with a subfamily of the `G` has the same colour. -/
lemma exists_translatedCube (C : Type*) [Finite C] (n : ℕ) :
    ∃ M : ℕ, ∀ d : Finset (Fin M) → C,
      ∃ (E : Finset (Fin M)) (G : Fin n → Finset (Fin M)),
        E.Nonempty ∧ (∀ i, (G i).Nonempty) ∧ (∀ i, Disjoint E (G i)) ∧
          (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧
          ∃ c, ∀ I : Finset (Fin n), d (E ∪ I.biUnion G) = c := by
  classical
  obtain ⟨M, hM⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin Bool C (Fin (n + 1))
  refine ⟨M, fun d ↦ ?_⟩
  obtain ⟨W, c, hc⟩ := hM fun x ↦ d {i | x i}
  set S : Finset (Fin M) := {i | W.idxFun i = Sum.inl true} with hS
  set X : Fin (n + 1) → Finset (Fin M) := fun j ↦ {i | W.idxFun i = Sum.inr j} with hX
  have hXne : ∀ j, (X j).Nonempty := by
    intro j
    obtain ⟨i, hi⟩ := W.proper j
    exact ⟨i, by simp [hX, hi]⟩
  have hXX : ∀ j j', j ≠ j' → Disjoint (X j) (X j') := by
    intro j j' hjj'
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact hjj' (Sum.inr_injective (hi.symm.trans hi'))
  have hSX : ∀ j, Disjoint S (X j) := by
    intro j
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hS, hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact absurd (hi.symm.trans hi') (by simp)
  have key : ∀ J : Finset (Fin (n + 1)), d (S ∪ J.biUnion X) = c := by
    intro J
    rw [← hc fun j ↦ decide (j ∈ J)]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_biUnion]
    simp only [hS, hX]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Combinatorics.Subspace.coe_apply]
    cases h : W.idxFun i with
    | inl b => cases b <;> simp
    | inr j => simp
  refine ⟨S ∪ X 0, fun i ↦ X i.succ, (hXne 0).mono Finset.subset_union_right,
    fun i ↦ hXne _, fun i ↦ ?_, fun i j hij ↦ hXX _ _ fun h ↦ hij (Fin.succ_injective _ h),
    c, fun I ↦ ?_⟩
  · exact Finset.disjoint_union_left.2 ⟨hSX _, hXX _ _ (Fin.succ_ne_zero i).symm⟩
  · convert key (insert 0 (I.image Fin.succ)) using 2
    ext i
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image, or_assoc]
    constructor
    · rintro (hi | hi | ⟨j, hj, hij⟩)
      · exact Or.inl hi
      · exact Or.inr ⟨0, Or.inl rfl, hi⟩
      · exact Or.inr ⟨j.succ, Or.inr ⟨j, hj, rfl⟩, hij⟩
    · rintro (hi | ⟨j, rfl | ⟨j', hj', rfl⟩, hij⟩)
      · exact Or.inl hi
      · exact Or.inr (Or.inl hij)
      · exact Or.inr (Or.inr ⟨j', hj', hij⟩)

/-- Iterating the translated cube canonizes the colour of a union of blocks in terms of the least
block that it contains. -/
lemma exists_minCanonical (C : Type*) [Finite C] (t : ℕ) :
    ∃ D : ℕ, ∀ d : Finset (Fin D) → C, ∃ E : Fin t → Finset (Fin D),
      (∀ i, (E i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        ∃ f : Fin t → C, ∀ (J : Finset (Fin t)) (hJ : J.Nonempty),
          d (J.biUnion E) = f (J.min' hJ) := by
  classical
  induction t with
  | zero =>
    refine ⟨0, fun d ↦ ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, Fin.elim0, fun J hJ ↦ ?_⟩⟩
    simp [Finset.eq_empty_of_isEmpty J] at hJ
  | succ t ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨M, hM⟩ := exists_translatedCube C D
    refine ⟨M, fun d ↦ ?_⟩
    obtain ⟨E₀, G, hE₀, hG, hE₀G, hGG, c, hc⟩ := hM d
    obtain ⟨I, hI, hII, f, hf⟩ := hD fun K ↦ d (K.biUnion G)
    refine ⟨Fin.cons E₀ fun j ↦ (I j).biUnion G, ?_, ?_, Fin.cons c f, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hE₀
      | succ j => simpa using (hI j).biUnion fun g _ ↦ hG g
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simpa using (Finset.disjoint_biUnion_right _ _ _).2 fun g _ ↦ hE₀G g
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simpa using
            (Finset.disjoint_biUnion_left _ _ _).2 fun g _ ↦ (hE₀G g).symm
        | succ j =>
          simp only [Fin.cons_succ]
          refine (Finset.disjoint_biUnion_left _ _ _).2 fun g hg ↦
            (Finset.disjoint_biUnion_right _ _ _).2 fun g' hg' ↦ hGG g g' fun hgg' ↦ ?_
          exact (hII i j fun h ↦ hij (congrArg Fin.succ h)).notMem_of_mem_left_finset hg
            (hgg' ▸ hg')
    · intro J hJ
      set K : Finset (Fin t) := {j | j.succ ∈ J} with hK
      have himage : J.erase 0 = K.image Fin.succ := by
        ext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp [hK, Fin.succ_ne_zero]
      have hbiUnion : (J.erase 0).biUnion (Fin.cons E₀ fun j ↦ (I j).biUnion G)
          = (K.biUnion I).biUnion G := by
        rw [himage, Finset.image_biUnion, Finset.biUnion_biUnion]
        simp
      by_cases h0 : (0 : Fin (t + 1)) ∈ J
      · have hmin : J.min' hJ = 0 := le_antisymm (Finset.min'_le _ _ h0) (Fin.zero_le _)
        rw [hmin]
        simp only [Fin.cons_zero]
        rw [← Finset.insert_erase h0, Finset.biUnion_insert]
        simp only [Fin.cons_zero]
        rw [hbiUnion]
        exact hc _
      · have hKne : K.Nonempty := by
          obtain ⟨i, hi⟩ := hJ
          induction i using Fin.cases with
          | zero => exact absurd hi h0
          | succ j => exact ⟨j, by simpa [hK] using hi⟩
        have hJK : J = K.image Fin.succ := by rw [← himage, Finset.erase_eq_of_notMem h0]
        have hmin : J.min' hJ = (K.min' hKne).succ := by
          refine le_antisymm ?_ ?_
          · refine Finset.min'_le _ _ ?_
            rw [hJK]
            exact Finset.mem_image_of_mem _ (K.min'_mem _)
          · refine Finset.le_min' _ _ _ fun y hy ↦ ?_
            rw [hJK, Finset.mem_image] at hy
            obtain ⟨j, hj, rfl⟩ := hy
            exact Fin.succ_le_succ_iff.2 (Finset.min'_le _ _ hj)
        rw [hmin]
        simp only [Fin.cons_succ]
        rw [← Finset.erase_eq_of_notMem h0, hbiUnion]
        exact hf K hKne

/-- The finite disjoint unions theorem: for every colouring of the subsets of a large enough
finite index set there are `m` pairwise disjoint nonempty blocks all of whose nonempty unions
receive the same colour. -/
lemma exists_monochromaticUnions (C : Type*) [Finite C] (m : ℕ) :
    ∃ D : ℕ, ∀ d : Finset (Fin D) → C, ∃ E : Fin m → Finset (Fin D),
      (∀ i, (E i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        ∃ c, ∀ J : Finset (Fin m), J.Nonempty → d (J.biUnion E) = c := by
  classical
  have := Fintype.ofFinite C
  obtain ⟨D, hD⟩ := exists_minCanonical C ((m - 1) * Fintype.card C + 1)
  refine ⟨D, fun d ↦ ?_⟩
  obtain ⟨E, hE, hEE, f, hf⟩ := hD d
  obtain ⟨c, -, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := Finset.univ)
      (t := (Finset.univ : Finset C)) (f := f) (n := m - 1) (fun a _ ↦ Finset.mem_univ _) (by
        simp only [Finset.card_univ, Fintype.card_fin]
        rw [Nat.mul_comm]
        omega)
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := {i | f i = c}) (n := m) (by omega)
  refine ⟨fun j ↦ E (T.orderEmbOfFin hTcard j), fun j ↦ hE _,
    fun i j hij ↦ hEE _ _ fun h ↦ hij ((T.orderEmbOfFin hTcard).injective h), c, fun J hJ ↦ ?_⟩
  rw [← Finset.image_biUnion, hf _ (hJ.image _)]
  obtain ⟨j, -, hj⟩ :=
    Finset.mem_image.1 (Finset.min'_mem _ (hJ.image (T.orderEmbOfFin hTcard)))
  rw [← hj]
  simpa using hTsub (T.orderEmbOfFin_mem hTcard j)

end FiniteUnions
end DensityHalesJewett

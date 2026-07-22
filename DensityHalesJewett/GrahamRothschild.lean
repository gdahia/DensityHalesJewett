/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Subspace
import Mathlib.Combinatorics.Compactness
public import Mathlib.Combinatorics.Hindman
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

def BlockWord := List ℕ

namespace BlockWord

instance : Monoid BlockWord where
  one := []
  mul := List.append
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_assoc := List.append_assoc

def toList (w : BlockWord) : List ℕ := w

@[simp]
lemma toList_one : toList (1 : BlockWord) = [] := rfl

@[simp]
lemma toList_mul (u v : BlockWord) : toList (u * v) = toList u ++ toList v := rfl

def singletonStream (r : ℕ) : Stream' BlockWord := fun n ↦ [r + n]

/-- Every finite product of the successive singleton words is nonempty and strictly increasing. -/
lemma mem_fp_singletonStream (r : ℕ) {l : BlockWord}
    (hl : l ∈ Hindman.FP (singletonStream r)) :
    l.toList.Pairwise (· < ·) ∧ l.toList ≠ [] ∧ ∀ x ∈ l.toList, r ≤ x := by
  generalize hs : singletonStream r = s at hl
  induction hl generalizing r with
  | head' s =>
      subst s
      change List.Pairwise (· < ·) [r] ∧ [r] ≠ [] ∧ ∀ x ∈ [r], r ≤ x
      simp
  | tail' s l hl ih =>
      have ht : s.tail = singletonStream (r + 1) := by
        subst s
        funext n
        change [r + (n + 1)] = [(r + 1) + n]
        rw [Nat.add_assoc, Nat.add_comm n 1, ← Nat.add_assoc]
      obtain ⟨hp, hn, hlo⟩ := ih (r + 1) ht.symm
      exact ⟨hp, hn, fun x hx ↦ (Nat.le_succ r).trans (hlo x hx)⟩
  | cons' s l hl ih =>
      have ht : s.tail = singletonStream (r + 1) := by
        subst s
        funext n
        change [r + (n + 1)] = [(r + 1) + n]
        rw [Nat.add_assoc, Nat.add_comm n 1, ← Nat.add_assoc]
      obtain ⟨hp, hn, hlo⟩ := ih (r + 1) ht.symm
      subst s
      change List.Pairwise (· < ·) (r :: l.toList) ∧ r :: l.toList ≠ [] ∧
        ∀ x ∈ r :: l.toList, r ≤ x
      refine ⟨List.pairwise_cons.2 ⟨?_, hp⟩, by simp, ?_⟩
      · intro x hx
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self r) (hlo x hx)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact le_rfl
        · exact (Nat.le_succ r).trans (hlo x hx)

/-- Concatenate the first `n` stream entries selected by a Boolean predicate. -/
def select (b : Stream' BlockWord) (p : ℕ → Bool) : ℕ → BlockWord
  | 0 => 1
  | n + 1 => (if p 0 then b.head else 1) * select b.tail (fun i ↦ p (i + 1)) n

lemma select_eq_one (b : Stream' BlockWord) (p : ℕ → Bool) {n : ℕ}
    (h : ∀ i < n, p i = false) : select b p n = 1 := by
  induction n generalizing b p with
  | zero => rfl
  | succ n ih =>
      rw [select, if_neg (by simpa using h 0 (by omega)), one_mul, ih]
      intro i hi
      exact h (i + 1) (by omega)

lemma select_mem_fp (b : Stream' BlockWord) (p : ℕ → Bool) {n : ℕ}
    (h : ∃ i < n, p i = true) : select b p n ∈ Hindman.FP b := by
  induction n generalizing b p with
  | zero => omega
  | succ n ih =>
      by_cases hp : p 0 = true
      · rw [select, if_pos hp]
        by_cases ht : ∃ i < n, p (i + 1) = true
        · exact Hindman.FP.cons b _ (ih b.tail (fun i ↦ p (i + 1)) ht)
        · rw [select_eq_one]
          · rw [mul_one]
            exact Hindman.FP.head b
          · intro i hi
            exact Bool.eq_false_iff.mpr fun hip ↦ ht ⟨i, hi, hip⟩
      · rw [select, if_neg hp, one_mul]
        apply Hindman.FP.tail
        apply ih
        obtain ⟨i, hi, hpi⟩ := h
        obtain rfl | i := i
        · exact (hp hpi).elim
        · exact ⟨i, by omega, hpi⟩

lemma mem_toFinset_select (b : Stream' BlockWord) (p : ℕ → Bool) (n x : ℕ) :
    x ∈ (select b p n).toList.toFinset ↔
      ∃ i < n, p i = true ∧ x ∈ (b i).toList.toFinset := by
  induction n generalizing b p with
  | zero =>
      rw [select]
      simp only [Nat.not_lt_zero, false_and, exists_const]
      rw [toList_one]
      simp
  | succ n ih =>
      rw [select]
      by_cases hp : p 0 = true
      · rw [if_pos hp]
        change x ∈ (b.head.toList ++ (select b.tail (fun i ↦ p (i + 1)) n).toList).toFinset ↔ _
        rw [List.toFinset_append, Finset.mem_union, ih]
        constructor
        · rintro (hx | ⟨i, hi, hpi, hx⟩)
          · exact ⟨0, by omega, hp, by simpa only [Stream'.head, Stream'.get] using hx⟩
          · exact ⟨i + 1, by omega, hpi,
              by simpa only [Stream'.tail, Stream'.get] using hx⟩
        · rintro ⟨i, hi, hpi, hx⟩
          obtain rfl | i := i
          · exact Or.inl (by simpa only [Stream'.head, Stream'.get] using hx)
          · exact Or.inr ⟨i, by omega, hpi,
              by simpa only [Stream'.tail, Stream'.get] using hx⟩
      · rw [if_neg hp]
        change x ∈ (select b.tail (fun i ↦ p (i + 1)) n).toList.toFinset ↔ _
        rw [ih]
        constructor
        · rintro ⟨i, hi, hpi, hx⟩
          exact ⟨i + 1, by omega, hpi,
            by simpa only [Stream'.tail, Stream'.get] using hx⟩
        · rintro ⟨i, hi, hpi, hx⟩
          obtain rfl | i := i
          · exact (hp hpi).elim
          · exact ⟨i, by omega, hpi,
              by simpa only [Stream'.tail, Stream'.get] using hx⟩

end BlockWord

/-- Infinite finite unions for ordered blocks, obtained from strong Hindman on increasing words. -/
private lemma exists_infinite_mono (C : Type*) [Finite C] [Nonempty C]
    (χ : Finset ℕ → C) (m : ℕ) :
    ∃ B : Fin m → Finset ℕ,
      (∀ i, (B i).Nonempty) ∧
      (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
      ∃ c, ∀ I : Finset (Fin m), I.Nonempty → χ (I.biUnion B) = c := by
  classical
  let colorClass (c : C) : Set BlockWord := {l |
    l.toList.Pairwise (· < ·) ∧ l.toList ≠ [] ∧ χ l.toList.toFinset = c}
  have hcover : Hindman.FP (BlockWord.singletonStream 0) ⊆ ⋃₀ Set.range colorClass := by
    intro l hl
    obtain ⟨hp, hn, _⟩ := BlockWord.mem_fp_singletonStream 0 hl
    refine Set.mem_sUnion_of_mem (t := colorClass (χ l.toList.toFinset)) ?_
      (Set.mem_range_self (χ l.toList.toFinset))
    exact ⟨hp, hn, rfl⟩
  obtain ⟨_, ⟨c, rfl⟩, b, hb⟩ :=
    Hindman.FP_partition_regular (BlockWord.singletonStream 0) (Set.range colorClass)
      (Set.finite_range colorClass) hcover
  let B : Fin m → Finset ℕ := fun i ↦ (b i).toList.toFinset
  refine ⟨B, ?_, ?_, c, ?_⟩
  · intro i
    obtain ⟨_, hn, _⟩ := hb (Hindman.FP.singleton b i)
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (b i).toList hn
    exact ⟨x, by simpa only [B, List.mem_toFinset] using hx⟩
  · intro i j hij x hx y hy
    obtain ⟨hp, _, _⟩ := hb (Hindman.FP.mul_two b i j hij)
    rw [BlockWord.toList_mul, List.pairwise_append] at hp
    exact hp.2.2 x (by simpa only [B, List.mem_toFinset, Stream'.get] using hx) y
      (by simpa only [B, List.mem_toFinset, Stream'.get] using hy)
  · intro I hI
    let J := I.map Fin.valEmbedding
    let p : ℕ → Bool := fun i ↦ decide (i ∈ J)
    have hp : ∃ i < m, p i = true := by
      obtain ⟨i, hi⟩ := hI
      refine ⟨i, i.isLt, ?_⟩
      simp only [p, decide_eq_true_eq, J, Finset.mem_map]
      exact ⟨i, hi, rfl⟩
    have hs := hb (BlockWord.select_mem_fp b p hp)
    rw [← hs.2.2]
    apply congrArg χ
    ext x
    rw [BlockWord.mem_toFinset_select, Finset.mem_biUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      refine ⟨i.val, i.isLt, ?_, by simpa only [B] using hx⟩
      simp only [p, decide_eq_true_eq, J, Finset.mem_map]
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, hpi, hx⟩
      simp only [p, decide_eq_true_eq, J, Finset.mem_map] at hpi
      obtain ⟨j, hj, hji⟩ := hpi
      refine ⟨j, hj, ?_⟩
      change x ∈ (b j.val).toList.toFinset
      change j.val = i at hji
      rw [hji]
      exact hx

/-- The finite-unions theorem in ordered block-sequence form. -/
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
      by_contra h
      push Not at h
      let support (s : Finset (Finset ℕ)) := s.biUnion id
      let length (s : Finset (Finset ℕ)) :=
        if hs : (support s).Nonempty then (support s).max' hs + 1 else 0
      have hlt (s : Finset (Finset ℕ)) (u : Finset ℕ) (hu : u ∈ s)
          (x : ℕ) (hx : x ∈ u) : x < length s := by
        have hxs : x ∈ support s := Finset.mem_biUnion.mpr ⟨u, hu, hx⟩
        dsimp only [length]
        rw [dif_pos ⟨x, hxs⟩]
        exact Nat.lt_succ_of_le (Finset.le_max' (support s) x hxs)
      let restrict (s : Finset (Finset ℕ)) (u : {u // u ∈ s}) : Finset (Fin (length s)) :=
        u.val.attach.map
          { toFun := fun x ↦ ⟨x.val, hlt s u.val u.prop x.val x.prop⟩
            inj' := fun x y hxy ↦ Subtype.ext <| Fin.ext_iff.mp hxy }
      let bad (L : ℕ) : Finset (Fin L) → C := Classical.choose (h L)
      let g (s : Finset (Finset ℕ)) (u : s) : C := bad (length s) (restrict s u)
      obtain ⟨χ, hχ⟩ := Finset.rado_selection_subtype
        (β := fun _ : Finset ℕ ↦ C) g
      obtain ⟨B, hBne, hBorder, c, hBc⟩ := exists_infinite_mono C χ m
      let unions : Finset (Finset ℕ) :=
        Finset.univ.image fun I : Finset (Fin m) ↦ I.biUnion B
      obtain ⟨t, hut, ht⟩ := hχ unions
      have hBi (i : Fin m) : B i ∈ t := hut <| by
        refine Finset.mem_image.mpr ⟨{i}, Finset.mem_univ _, ?_⟩
        simp
      let B' : Fin m → Finset (Fin (length t)) := fun i ↦ restrict t ⟨B i, hBi i⟩
      have hB'ne : ∀ i, (B' i).Nonempty := by
        intro i
        obtain ⟨x, hx⟩ := hBne i
        refine ⟨⟨x, hlt t (B i) (hBi i) x hx⟩, ?_⟩
        exact Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
      have hB'order : ∀ i j, i < j → ∀ x ∈ B' i, ∀ y ∈ B' j, x < y := by
        intro i j hij x hx y hy
        simp only [B', restrict, Finset.mem_map] at hx hy
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        exact hBorder i j hij x' x'.prop y' y'.prop
      obtain ⟨I, hI, hneq⟩ :=
        Classical.choose_spec (h (length t)) B' hB'ne hB'order c
      apply hneq
      let u := I.biUnion B
      have hu_unions : u ∈ unions := by
        exact Finset.mem_image.mpr ⟨I, Finset.mem_univ _, rfl⟩
      have hu_t : u ∈ t := hut hu_unions
      have hunion : I.biUnion B' = restrict t ⟨u, hu_t⟩ := by
        ext x
        simp only [Finset.mem_biUnion, B', restrict, Finset.mem_map]
        constructor
        · rintro ⟨i, hi, y, hy, hyx⟩
          refine ⟨⟨y, Finset.mem_biUnion.mpr ⟨i, hi, y.prop⟩⟩, Finset.mem_attach _ _, ?_⟩
          exact Fin.ext <| congrArg Fin.val hyx
        · rintro ⟨y, hy, hyx⟩
          obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp y.prop
          refine ⟨i, hi, ⟨⟨y, hyi⟩, Finset.mem_attach _ _, ?_⟩⟩
          exact Fin.ext <| congrArg Fin.val hyx
      rw [hunion]
      change bad (length t) (restrict t ⟨u, hu_t⟩) = c
      rw [← hBc I hI]
      exact (ht ⟨u, hu_unions⟩).symm

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

/-- A block-canonization dimension. -/
opaque canonizationBound (alphabet colors blocks : ℕ) : ℕ

/-- Block canonization: inside a suitable subspace, the color of a line depends only on its
variable directions and not on its fixed letters. -/
lemma canonize (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (L n : ℕ)
    (hn : canonizationBound (Fintype.card α) (Fintype.card C) L ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin L) α (Fin n),
      ∀ p q : Combinatorics.Line α (Fin L), variableSet p = variableSet q →
        χ (Subspace.mapLine V p) = χ (Subspace.mapLine V q) := by
  sorry

/-- A Graham--Rothschild dimension for colorings of combinatorial lines. -/
opaque bound (alphabet colors dimension : ℕ) : ℕ

/-- The line case of the Graham--Rothschild theorem. -/
lemma lines (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C]
    [DecidableEq α] (m n : ℕ) (hm : 1 ≤ m)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  sorry

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

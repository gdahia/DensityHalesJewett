/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Main
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.Indexes

/-!
# Arithmetic progressions from combinatorial lines

Fixed-length base encoding and the digital transfer from density Hales--Jewett to Szemeredi's
theorem on finite intervals.
-/

@[expose] public section

open Finset
open Combinatorics

namespace Combinatorics

/-- A nonconstant arithmetic progression of length `k` in an additive monoid. -/
@[ext]
structure ArithmeticProgression (α : Type*) [AddMonoid α] (k : ℕ) where
  /-- The initial term of the arithmetic progression. -/
  start : α
  /-- The common difference of the arithmetic progression. -/
  diff : α
  diff_ne_zero : diff ≠ 0

namespace ArithmeticProgression

/-- The term of `P` indexed by `i`. -/
def term {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (i : Fin k) : α :=
  P.start + (i : ℕ) • P.diff

/-- The proposition that every term of `P` belongs to `s`. -/
def IsSubset {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (s : Set α) : Prop :=
  ∀ i, P.term i ∈ s

end ArithmeticProgression
end Combinatorics

namespace DensityHalesJewett

/-- Encode a fixed-length word as a natural number in base `k`. -/
def baseEncode (k m : ℕ) (x : Fin m → Fin k) : ℕ :=
  ∑ i, (x i : ℕ) * k ^ (i : ℕ)

lemma baseEncode_eq_ofDigits (k m : ℕ) (x : Fin m → Fin k) :
    baseEncode k m x = Nat.ofDigits k (List.ofFn fun i ↦ (x i : ℕ)) := by
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]
  simp only [List.get_ofFn]
  unfold baseEncode
  refine Fintype.sum_equiv (finCongr List.length_ofFn.symm) _ _ ?_
  intro i
  congr 2

/-- A base-`k` encoding of an `m`-digit word lies below `k ^ m`. -/
lemma baseEncode_lt_pow {k m : ℕ} (hk : 1 < k) (x : Fin m → Fin k) :
    baseEncode k m x < k ^ m := by
  rw [baseEncode_eq_ofDigits]
  apply Nat.mapsTo_ofDigits hk m
  simp

/-- Fixed-length base-`k` encoding is a bijection with the initial interval of length `k^m`. -/
noncomputable def baseEncodeEquiv (k m : ℕ) (hk : 1 ≤ k) :
    (Fin m → Fin k) ≃ Fin (k ^ m) := by
  classical
  by_cases hk_one : k = 1
  · subst k
    simpa using (Equiv.ofUnique (Fin m → Fin 1) (Fin 1))
  have hk_two : 1 < k := lt_of_le_of_ne hk (Ne.symm hk_one)
  let encode (x : Fin m → Fin k) : Fin (k ^ m) := ⟨baseEncode k m x, baseEncode_lt_pow hk_two x⟩
  apply Equiv.ofBijective encode
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro x y hxy
    apply funext
    intro i
    apply Fin.ext
    change (fun j ↦ (x j : ℕ)) i = (fun j ↦ (y j : ℕ)) i
    apply congrArg (fun f : Fin m → ℕ ↦ f i)
    apply List.ofFn_injective
    apply Nat.injOn_ofDigits hk_two m
    · simp
    · simp
    · simpa only [← baseEncode_eq_ofDigits, encode] using
        congrArg Fin.val hxy
  · simp

@[simp]
lemma baseEncodeEquiv_apply (k m : ℕ) (hk : 2 ≤ k) (x : Fin m → Fin k) :
    (baseEncodeEquiv k m (one_le_two.trans hk) x : ℕ) = baseEncode k m x := by
  classical
  by_cases hk_one : k = 1
  · grind
  · simp [baseEncodeEquiv, hk_one]

namespace Line

/-- A base-encoded combinatorial line is a nonconstant arithmetic progression. -/
lemma baseEncode_isArithmeticProgression {k m : ℕ} (hk : 1 ≤ k)
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ∃ P : Combinatorics.ArithmeticProgression ℕ k,
      ∀ a, P.term a = baseEncode k m (l a) := by
  let d := ∑ i : Fin m, if l.idxFun i = none then k ^ (i : ℕ) else 0
  refine ⟨
    { start := baseEncode k m (l ⟨0, hk⟩)
      diff := d
      diff_ne_zero := ?_ }, ?_⟩
  · apply Nat.ne_of_gt
    apply Finset.sum_pos'
    · intro i _
      exact Nat.zero_le _
    · obtain ⟨i, hi⟩ := l.proper
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simp [hi, Nat.zero_lt_of_lt hk]
  · intro a
    change baseEncode k m (l ⟨0, hk⟩) + (a : ℕ) • d = baseEncode k m (l a)
    unfold baseEncode
    rw [nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : l.idxFun i = none
    · simp [Combinatorics.Line.coe_apply, hi]
    · cases hli : l.idxFun i with
      | none => exact (hi hli).elim
      | some b => simp [Combinatorics.Line.coe_apply, hli]

end Line

/-- A sufficiently dense initial interval has a complete digit block with at least half the
ambient density. -/
lemma exists_dense_digitBlock {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 2 * K / δ ≤ N) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : δ * N ≤ #A) :
    ∃ q : ℕ, (q + 1) * K ≤ N ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
  let Q := N / K
  let S := A ∩ Finset.range (Q * K)
  have htail : (#(A \ Finset.range (Q * K)) : ℝ) < K := by
    norm_cast
    refine (Finset.card_le_card (t := Finset.Ico (Q * K) N) ?_).trans_lt ?_
    · intro x hx
      rw [Finset.mem_Ico]
      rw [Finset.mem_sdiff, Finset.mem_range] at hx
      exact ⟨Nat.le_of_not_gt hx.2, Finset.mem_range.mp (hAN hx.1)⟩
    · rw [Nat.card_Ico]
      simpa only [Q, Nat.mod_eq_sub_mul_div, Nat.mul_comm] using
        Nat.mod_lt N (Nat.zero_lt_of_lt hK)
  have hS : δ / 2 * N ≤ (#S : ℝ) := by
    rw [← Finset.card_inter_add_card_sdiff A (Finset.range (Q * K))] at hA
    push_cast at hA
    dsimp only [S]
    nlinarith [htail, (div_le_iff₀ hδ).mp hN]
  have hmap : ∀ x ∈ S, x / K ∈ Finset.range Q := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_range] at hx
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).2 hx.2)
  obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Finset.range Q,
      δ / 2 * K ≤ ∑ x ∈ S with x / K = q, (1 : ℝ) := by
    apply Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (M := ℝ) (s := S) (t := Finset.range Q) (f := fun x ↦ x / K)
      (w := fun _ ↦ 1) (b := δ / 2 * K) hmap
    · obtain ⟨x, hx⟩ : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hSempty
        rw [hSempty, Finset.card_empty, Nat.cast_zero] at hS
        apply (not_lt_of_ge hS)
        apply mul_pos
        · positivity
        · apply lt_of_lt_of_le _ hN
          positivity
      exact ⟨x / K, hmap x hx⟩
    · simp only [Finset.card_range, nsmul_eq_mul, Finset.sum_const, mul_one]
      apply le_trans _ hS
      rw [← mul_assoc, mul_comm (Q : ℝ) (δ / 2), mul_assoc]
      apply mul_le_mul_of_nonneg_left
      · norm_cast
        exact Nat.div_mul_le_self N K
      · positivity
  refine ⟨q, ?_, ?_⟩
  · exact (Nat.mul_le_mul_right K (Nat.succ_le_iff.mp (Finset.mem_range.mp hqQ))).trans
      (Nat.div_mul_le_self N K)
  · convert hq using 1
    norm_cast
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    ext x
    dsimp only [S]
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hxA, hxlo, hxhi⟩
      refine ⟨⟨hxA, hxhi.trans_le ?_⟩, ?_⟩
      · exact Nat.mul_le_mul_right K
          (Nat.succ_le_iff.mp (Finset.mem_range.mp hqQ))
      · apply Nat.le_antisymm
        · exact Nat.lt_succ_iff.mp
            ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).2 hxhi)
        · exact (Nat.le_div_iff_mul_le (Nat.zero_lt_of_lt hK)).2 hxlo
    · rintro ⟨⟨hxA, _⟩, hxq⟩
      refine ⟨hxA, ?_, ?_⟩
      · rw [← hxq]
        simpa [Nat.mul_comm] using Nat.mul_div_le x K
      · rw [← hxq]
        exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).mp (Nat.lt_succ_self _)

end DensityHalesJewett

namespace Combinatorics.ArithmeticProgression

/-- A threshold for the density theorem for arithmetic progressions of length `k`. -/
noncomputable def densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ :=
  ⌈2 * (k ^ Combinatorics.Line.densityTheoremBound k (δ / 2) : ℕ) / δ⌉₊

theorem exists_of_density_nat (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hAδ : δ * n ≤ #A) :
    ∃ P : ArithmeticProgression ℕ k, P.IsSubset (A : Set ℕ) := by
  classical
  have hk_two : 2 ≤ k := by grind
  have hk_one : 1 ≤ k := one_le_two.trans hk_two
  let m := Combinatorics.Line.densityTheoremBound k (δ / 2)
  let K := k ^ m
  obtain ⟨q, _, hqA⟩ : ∃ q : ℕ, (q + 1) * K ≤ n ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
    refine DensityHalesJewett.exists_dense_digitBlock ?_ hδ ?_ A hAn hAδ
    · exact one_le_pow₀ hk_one
    · apply Nat.le_of_ceil_le
      simpa only [densityTheoremBound, m, K] using hn
  let encode (x : Fin m → Fin k) := q * K + DensityHalesJewett.baseEncode k m x
  let B := Finset.univ.filter fun x : Fin m → Fin k ↦ encode x ∈ A
  let encodeOnB (x : Fin m → Fin k) (_ : x ∈ B) := encode x
  have hBcard : #B = #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
    apply Finset.card_bij encodeOnB
    · intro x hx
      dsimp only [encodeOnB, encode]
      rw [Finset.mem_filter] at hx
      refine Finset.mem_inter.mpr ⟨hx.2, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, ?_⟩⟩
      rw [add_mul, one_mul]
      apply Nat.add_lt_add_left
      simpa only [K] using DensityHalesJewett.baseEncode_lt_pow hk_two x
    · intro x _ y _ hxy
      dsimp only [encodeOnB, encode] at hxy
      apply (DensityHalesJewett.baseEncodeEquiv k m hk_one).injective
      apply Fin.ext
      rw [DensityHalesJewett.baseEncodeEquiv_apply k m hk_two x,
        DensityHalesJewett.baseEncodeEquiv_apply k m hk_two y]
      exact Nat.add_left_cancel hxy
    · intro y hy
      rw [Finset.mem_inter, Finset.mem_Ico] at hy
      have hz : y - q * K < K := by
        rw [Nat.sub_lt_iff_lt_add hy.2.1]
        simpa only [add_mul, one_mul, Nat.add_comm] using hy.2.2
      let z : Fin K := ⟨y - q * K, hz⟩
      let x := (DensityHalesJewett.baseEncodeEquiv k m hk_one).symm z
      have hxencode : DensityHalesJewett.baseEncode k m x = y - q * K := by
        rw [← DensityHalesJewett.baseEncodeEquiv_apply k m hk_two x]
        exact congrArg Fin.val (Equiv.apply_symm_apply
          (DensityHalesJewett.baseEncodeEquiv k m hk_one) z)
      dsimp only [encodeOnB, encode]
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · dsimp only [encode]
        rw [hxencode, Nat.add_sub_of_le hy.2.1]
        exact hy.1
      · rw [hxencode, Nat.add_sub_of_le hy.2.1]
  obtain ⟨l, hl⟩ : ∃ l : Combinatorics.Line (Fin k) (Fin m), ∀ x : Fin k, l x ∈ B := by
    apply Combinatorics.Line.exists_of_density (Fin k) (δ / 2)
    · positivity
    · simp [m]
    · rw [Fintype.card_fin, hBcard]
      simpa only [K, Nat.cast_pow] using hqA
  obtain ⟨P, hP⟩ := DensityHalesJewett.Line.baseEncode_isArithmeticProgression hk_one l
  refine ⟨
    { start := q * K + P.start
      diff := P.diff
      diff_ne_zero := P.diff_ne_zero }, ?_⟩
  intro a
  change (q * K + P.start) + (a : ℕ) • P.diff ∈ A
  rw [add_assoc]
  change q * K + P.term a ∈ A
  rw [hP]
  exact (Finset.mem_filter.mp (hl a)).2

end Combinatorics.ArithmeticProgression

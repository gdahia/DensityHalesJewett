/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Szemeredi

/-!
# Many arithmetic progressions in dense sets

Varnavides' averaging argument upgrades Szemerédi's theorem from the existence of one arithmetic
progression in a dense set to a quadratic lower bound on the number of such progressions.
-/

@[expose] public section

open Finset

namespace Combinatorics.ArithmeticProgression

/-- The pairs `(a, d)` that parametrize nonconstant `k`-term arithmetic progressions
contained in `A`. -/
def containedProgressions (k n : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter fun p ↦
    p.2 ≠ 0 ∧ ∀ i : Fin k, p.1 + (i : ℕ) * p.2 ∈ A

/-- The indices at which the finite progression parametrized by `p` meets `A`. -/
def indicesIn (m : ℕ) (A : Finset ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (range m).filter fun i ↦ p.1 + i * p.2 ∈ A

/-- Finite progressions of length `m`, positive difference at most `D`, and lying in
`range n`. We use the slightly stronger endpoint condition `a + m * d ≤ n`. -/
def grids (m n D : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ Icc 1 D).filter fun p ↦ p.1 + m * p.2 ≤ n

/-- Incidences between a grid and one of its indices whose image lies in `A`. -/
def gridIncidences (m n D : ℕ) (A : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (grids m n D ×ˢ range m).filter fun gi ↦
    gi.1.1 + gi.2 * gi.1.2 ∈ A

lemma card_gridIncidences (m n D : ℕ) (A : Finset ℕ) :
    #(gridIncidences m n D A) =
      ∑ p ∈ grids m n D, #(indicesIn m A p) := by
  classical
  simp only [gridIncidences, indicesIn, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_filter]

/-- The grids on which `A` has density at least `δ`. -/
noncomputable def denseGrids (δ : ℝ) (m n D : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (grids m n D).filter fun p ↦ δ * m ≤ #(indicesIn m A p)

lemma card_grids_le (m n D : ℕ) :
    #(grids m n D) ≤ n * D := by
  refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
  simp [Nat.card_Icc]

lemma card_gridIncidences_upper_bound (δ : ℝ) (hδ : 0 ≤ δ) (m n D : ℕ)
    (A : Finset ℕ) :
    (#(gridIncidences m n D A) : ℝ) ≤
      δ * m * #(grids m n D) + m * #(denseGrids δ m n D A) := by
  rw [card_gridIncidences, Nat.cast_sum]
  calc
    _ ≤ ∑ p ∈ grids m n D,
        (δ * m + if p ∈ denseGrids δ m n D A then (m : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpdense : p ∈ denseGrids δ m n D A
      · rw [if_pos hpdense]
        have hcard : #(indicesIn m A p) ≤ m := by
          change #((range m).filter fun i ↦ p.1 + i * p.2 ∈ A) ≤ m
          simpa only [Finset.card_range] using
            Finset.card_le_card
              (Finset.filter_subset (p := fun i ↦ p.1 + i * p.2 ∈ A) (range m))
        have hcardreal : (#(indicesIn m A p) : ℝ) ≤ m := by exact_mod_cast hcard
        nlinarith
      · simp only [if_neg hpdense, add_zero]
        rw [denseGrids, Finset.mem_filter] at hpdense
        exact le_of_lt (not_le.mp fun h ↦ hpdense ⟨hp, h⟩)
    _ = δ * m * #(grids m n D) + m * #(denseGrids δ m n D A) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hindicator :
          ∑ x ∈ grids m n D,
              (if x ∈ denseGrids δ m n D A then (m : ℝ) else 0) =
            m * #(denseGrids δ m n D A) := by
        rw [← Finset.sum_filter]
        have hfilter :
            (grids m n D).filter (· ∈ denseGrids δ m n D A) =
              denseGrids δ m n D A := by
          ext p
          simp [denseGrids]
        rw [hfilter]
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [hindicator]
      ring

lemma card_gridIncidences_lower_bound (m n D W : ℕ) (hW : m * D ≤ W)
    (A : Finset ℕ) (hAn : A ⊆ range n) :
    #(A ∩ Icc W (n - W)) * D * m ≤ #(gridIncidences m n D A) := by
  let domain := ((A ∩ Icc W (n - W)) ×ˢ Icc 1 D) ×ˢ range m
  let f : ((ℕ × ℕ) × ℕ) → ((ℕ × ℕ) × ℕ) :=
    fun x ↦ ((x.1.1 - x.2 * x.1.2, x.1.2), x.2)
  have hdomaincard :
      #domain = #(A ∩ Icc W (n - W)) * D * m := by
    simp [domain, Nat.card_Icc]
  rw [← hdomaincard]
  change #domain ≤ #(gridIncidences m n D A)
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    change x ∈ domain at hx
    dsimp only [domain] at hx
    rw [Finset.mem_product, Finset.mem_product] at hx
    change f x ∈ gridIncidences m n D A
    rw [gridIncidences, Finset.mem_filter, Finset.mem_product, grids,
      Finset.mem_filter, Finset.mem_product]
    rcases hx with ⟨⟨hxA, hxd⟩, hxi⟩
    rw [Finset.mem_inter, Finset.mem_Icc] at hxA
    rw [Finset.mem_Icc] at hxd
    rw [Finset.mem_range] at hxi
    have hidW : x.2 * x.1.2 ≤ W := by
      exact (Nat.mul_le_mul hxi.le hxd.2).trans hW
    have hidX : x.2 * x.1.2 ≤ x.1.1 := hidW.trans hxA.2.1
    refine ⟨?_, ?_⟩
    · refine ⟨?_, Finset.mem_range.mpr hxi⟩
      refine ⟨⟨Finset.mem_range.mpr ?_, Finset.mem_Icc.mpr hxd⟩, ?_⟩
      · exact (Nat.sub_le _ _).trans_lt (Finset.mem_range.mp (hAn hxA.1))
      · dsimp only [f, Prod.fst, Prod.snd]
        have hmdW := (Nat.mul_le_mul_left m hxd.2).trans hW
        omega
    · dsimp only [f, Prod.fst, Prod.snd]
      rw [Nat.sub_add_cancel hidX]
      exact hxA.1
  · intro x hx y hy hxy
    simp only [f, Prod.mk.injEq] at hxy
    change x ∈ domain at hx
    change y ∈ domain at hy
    dsimp only [domain] at hx hy
    rw [Finset.mem_product, Finset.mem_product] at hx hy
    rcases hx with ⟨⟨hxA, hxd⟩, hxi⟩
    rcases hy with ⟨⟨hyA, hyd⟩, hyi⟩
    rw [Finset.mem_inter, Finset.mem_Icc] at hxA hyA
    rw [Finset.mem_Icc] at hxd hyd
    rw [Finset.mem_range] at hxi hyi
    have hxsub : x.2 * x.1.2 ≤ x.1.1 :=
      (Nat.mul_le_mul hxi.le hxd.2).trans hW |>.trans hxA.2.1
    have hysub : y.2 * y.1.2 ≤ y.1.1 :=
      (Nat.mul_le_mul hyi.le hyd.2).trans hW |>.trans hyA.2.1
    apply Prod.ext
    · apply Prod.ext
      · rw [← Nat.sub_add_cancel hxsub, ← Nat.sub_add_cancel hysub, hxy.1.1,
          hxy.1.2, hxy.2]
      · exact hxy.1.2
    · exact hxy.2

lemma card_inter_interior (n W : ℕ) (A : Finset ℕ) (hAn : A ⊆ range n) :
    #A ≤ #(A ∩ Icc W (n - W)) + 2 * W := by
  have houtside :
      A \ Icc W (n - W) ⊆ range W ∪ Ico (n - W) n := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hx
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    have hxn := Finset.mem_range.mp (hAn hx.1)
    omega
  have houtcard : #(A \ Icc W (n - W)) ≤ 2 * W := by
    refine (Finset.card_le_card houtside).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    rw [Finset.card_range, Nat.card_Ico]
    omega
  rw [← Finset.card_inter_add_card_sdiff A (Icc W (n - W))]
  omega

lemma denseGrids_card_lower_bound (δ : ℝ) (hδ : 0 < δ) (m n D W : ℕ)
    (hm : 0 < m) (hW : m * D ≤ W) (hWsmall : 8 * W ≤ δ * n)
    (A : Finset ℕ) (hAn : A ⊆ range n) (hA : δ * n ≤ #A) :
    δ / 4 * n * D ≤ #(denseGrids (δ / 2) m n D A) := by
  have hinter : δ * n - 2 * W ≤ (#(A ∩ Icc W (n - W)) : ℝ) := by
    have := card_inter_interior n W A hAn
    have thisreal :
        (#A : ℝ) ≤ #(A ∩ Icc W (n - W)) + 2 * W := by exact_mod_cast this
    linarith
  have hincidence :
      ((#(A ∩ Icc W (n - W)) * D * m : ℕ) : ℝ) ≤
        #(gridIncidences m n D A) := by
    exact_mod_cast card_gridIncidences_lower_bound m n D W hW A hAn
  push_cast at hincidence
  have hupper := card_gridIncidences_upper_bound (δ / 2) (by positivity) m n D A
  have hgrids : (#(grids m n D) : ℝ) ≤ n * D := by
    exact_mod_cast card_grids_le m n D
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hD : (0 : ℝ) ≤ D := by positivity
  have hinter_mul :
      (δ * n - 2 * W) * D * m ≤
        (#(A ∩ Icc W (n - W)) : ℝ) * D * m := by
    gcongr
  have hgridterm :
      δ / 2 * m * (#(grids m n D) : ℝ) ≤ δ / 2 * m * (n * D) := by
    gcongr
  have hchain :
      (δ * n - 2 * W) * D * m ≤
        δ / 2 * m * (n * D) + m * #(denseGrids (δ / 2) m n D A) :=
    hinter_mul.trans (hincidence.trans (hupper.trans
      (add_le_add hgridterm le_rfl)))
  nlinarith [hchain, mul_nonneg (show (0 : ℝ) ≤ D by positivity) hmreal.le]

lemma exists_containedProgression_of_dense_indices (k : ℕ) (hk : 3 ≤ k)
    (δ : ℝ) (hδ : 0 < δ) (m n : ℕ) (hm : densityTheoremBound k δ ≤ m)
    (A : Finset ℕ) (hAn : A ⊆ range n) (p : ℕ × ℕ) (hp : p.2 ≠ 0)
    (hdense : δ * m ≤ #(indicesIn m A p)) :
    ∃ q ∈ containedProgressions k n A,
      ∃ P : ArithmeticProgression ℕ k,
        P.start < m ∧ P.diff < m ∧
        q = (p.1 + P.start * p.2, P.diff * p.2) := by
  obtain ⟨P, hP⟩ := exists_of_density_nat k hk δ hδ m hm (indicesIn m A p)
    (by simp [indicesIn]) hdense
  have hPzero := hP ⟨0, by omega⟩
  have hPone := hP ⟨1, by omega⟩
  change P.term ⟨0, by omega⟩ ∈ indicesIn m A p at hPzero
  change P.term ⟨1, by omega⟩ ∈ indicesIn m A p at hPone
  rw [indicesIn, Finset.mem_filter] at hPzero hPone
  refine ⟨(p.1 + P.start * p.2, P.diff * p.2), ?_, P, ?_, ?_, rfl⟩
  · rw [containedProgressions, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_, ?_⟩
    · unfold ArithmeticProgression.term at hPzero
      simpa only [Nat.zero_eq, zero_nsmul, Nat.add_zero] using
        Finset.mem_range.mp (hAn hPzero.2)
    · unfold ArithmeticProgression.term at hPone
      rw [one_nsmul] at hPone
      have := Finset.mem_range.mp (hAn hPone.2)
      exact lt_of_le_of_lt
        (Nat.mul_le_mul_right p.2 (Nat.le_add_left P.diff P.start))
        ((Nat.le_add_left _ p.1).trans_lt this)
    · exact mul_ne_zero P.diff_ne_zero hp
    · intro i
      have hi := hP i
      change P.term i ∈ indicesIn m A p at hi
      rw [indicesIn, Finset.mem_filter] at hi
      unfold ArithmeticProgression.term at hi
      rw [nsmul_eq_mul] at hi
      change P.start + i.val * P.diff ∈ range m ∧
        p.1 + (P.start + i.val * P.diff) * p.2 ∈ A at hi
      change p.1 + P.start * p.2 + i.val * (P.diff * p.2) ∈ A
      ring_nf at hi ⊢
      exact hi.2
  · unfold ArithmeticProgression.term at hPzero
    simpa only [Nat.zero_eq, zero_nsmul, Nat.add_zero] using
      Finset.mem_range.mp hPzero.1
  · unfold ArithmeticProgression.term at hPone
    rw [one_nsmul] at hPone
    have := Finset.mem_range.mp hPone.1
    omega

lemma denseGrids_card_le_containedProgressions_mul (k : ℕ) (hk : 3 ≤ k)
    (δ : ℝ) (hδ : 0 < δ) (m n D : ℕ) (hm : densityTheoremBound k δ ≤ m)
    (A : Finset ℕ) (hAn : A ⊆ range n) :
    #(denseGrids δ m n D A) ≤ #(containedProgressions k n A) * m ^ 2 := by
  classical
  let S := denseGrids δ m n D A
  have hex (p : ↥S) :
      ∃ q ∈ containedProgressions k n A,
        ∃ P : ArithmeticProgression ℕ k,
          P.start < m ∧ P.diff < m ∧
          q = (p.1.1 + P.start * p.1.2, P.diff * p.1.2) := by
    have hp := p.2
    dsimp only [S] at hp
    change p.1 ∈ (grids m n D).filter
      (fun r ↦ δ * m ≤ #(indicesIn m A r)) at hp
    rw [Finset.mem_filter] at hp
    refine exists_containedProgression_of_dense_indices k hk δ hδ m n hm A hAn p.1 ?_ hp.2
    rw [grids, Finset.mem_filter, Finset.mem_product] at hp
    exact ne_of_gt (Finset.mem_Icc.mp hp.1.1.2).1
  let q (p : ↥S) := (hex p).choose
  have hq (p : ↥S) :
      q p ∈ containedProgressions k n A ∧
        ∃ P : ArithmeticProgression ℕ k,
          P.start < m ∧ P.diff < m ∧
          q p = (p.1.1 + P.start * p.1.2, P.diff * p.1.2) :=
    (hex p).choose_spec
  let P (p : ↥S) := (hq p).2.choose
  have hP (p : ↥S) :
      (P p).start < m ∧ (P p).diff < m ∧
        q p = (p.1.1 + (P p).start * p.1.2, (P p).diff * p.1.2) :=
    (hq p).2.choose_spec
  have hfiber (y : ℕ × ℕ) :
      #{p ∈ (Finset.univ : Finset ↥S) | q p = y} ≤ m ^ 2 := by
    rw [pow_two, ← Finset.card_range (n := m), ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun p ↦ ((P p).start, (P p).diff))
    · intro p hp
      change ((P p).start, (P p).diff) ∈ range m ×ˢ range m
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨(hP p).1, (hP p).2.1⟩
    · intro p hp r hr hpr
      change p ∈ (Finset.univ : Finset ↥S).filter (fun p ↦ q p = y) at hp
      change r ∈ (Finset.univ : Finset ↥S).filter (fun p ↦ q p = y) at hr
      rw [Finset.mem_filter] at hp hr
      have hprstart : (P p).start = (P r).start := by
        simpa using congrArg Prod.fst hpr
      have hprdiff : (P p).diff = (P r).diff := by
        simpa using congrArg Prod.snd hpr
      have hqeq : q p = q r := hp.2.trans hr.2.symm
      rw [(hP p).2.2, (hP r).2.2, hprstart, hprdiff] at hqeq
      have hqdiff := congrArg Prod.snd hqeq
      have hdiff : p.1.2 = r.1.2 := by
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (P r).diff_ne_zero) hqdiff
      apply Subtype.ext
      apply Prod.ext
      · have hqstart := congrArg Prod.fst hqeq
        rw [hdiff] at hqstart
        exact Nat.add_right_cancel hqstart
      · exact hdiff
  calc
    #S = ∑ y ∈ (Finset.univ.image q),
        #{p ∈ (Finset.univ : Finset ↥S) | q p = y} := by
      rw [← Finset.card_eq_sum_card_image]
      simp
    _ ≤ ∑ _y ∈ (Finset.univ.image q), m ^ 2 := by
      exact Finset.sum_le_sum fun y _ ↦ hfiber y
    _ = #(Finset.univ.image q) * m ^ 2 := by simp
    _ ≤ #(containedProgressions k n A) * m ^ 2 := by
      apply Nat.mul_le_mul_right
      apply Finset.card_le_card
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨p, _, rfl⟩ := hy
      exact (hq p).1

/-- The positive proportion of progressions supplied by Varnavides' argument. -/
noncomputable def supersaturationConstant (k : ℕ) (δ : ℝ) : ℝ :=
  let m := densityTheoremBound k (δ / 2) + 1
  let C := ⌈16 * (m : ℝ) / δ⌉₊
  δ / (8 * C * m ^ 2)

/-- A threshold above which Varnavides' quadratic progression count holds. -/
noncomputable def supersaturationBound (k : ℕ) (δ : ℝ) : ℕ :=
  let m := densityTheoremBound k (δ / 2) + 1
  2 * ⌈16 * (m : ℝ) / δ⌉₊

/-- Varnavides' supersaturation consequence of Szemerédi's theorem: a dense subset of
`range n` contains a positive proportion of all pairs parametrizing `k`-term arithmetic
progressions. -/
theorem exists_many_of_density_nat (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : supersaturationBound k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hA : δ * n ≤ #A) :
    supersaturationConstant k δ * n ^ 2 ≤ #(containedProgressions k n A) := by
  let m := densityTheoremBound k (δ / 2) + 1
  let C := ⌈16 * (m : ℝ) / δ⌉₊
  change 2 * C ≤ n at hn
  change δ / (8 * C * m ^ 2) * n ^ 2 ≤ #(containedProgressions k n A)
  let D := n / C
  let W := m * D
  have hm : 0 < m := by simp [m]
  have hC : 0 < C := by
    dsimp only [C]
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  have hCn : C ≤ n := by omega
  have hD : 0 < D := by
    dsimp only [D]
    exact Nat.div_pos hCn hC
  have hCD : C * D ≤ n := by
    simpa only [D, Nat.mul_comm] using Nat.div_mul_le_self n C
  have hCbound : (16 : ℝ) * m ≤ δ * C := by
    have hceil : (16 : ℝ) * m / δ ≤ C := by
      simpa only [C] using Nat.le_ceil (16 * (m : ℝ) / δ)
    have := (div_le_iff₀ hδ).mp hceil
    simpa only [mul_comm] using this
  have hWsmall : (8 : ℝ) * W ≤ δ * n := by
    dsimp only [W]
    push_cast
    have hCDreal : (C : ℝ) * D ≤ n := by exact_mod_cast hCD
    have hboundD := mul_le_mul_of_nonneg_right hCbound (show (0 : ℝ) ≤ D by positivity)
    have hboundn := mul_le_mul_of_nonneg_left hCDreal hδ.le
    nlinarith
  have hgood := denseGrids_card_lower_bound δ hδ m n D W hm (by simp [W])
    hWsmall A hAn hA
  have hmany := denseGrids_card_le_containedProgressions_mul k hk (δ / 2)
    (by positivity) m n D (by simp [m]) A hAn
  have hnCD : (n : ℝ) ≤ 2 * C * D := by
    have hmod := Nat.mod_lt n hC
    have hdecomp := Nat.div_add_mod n C
    have hnle : n ≤ C * (D + 1) := by
      change C * D + n % C = n at hdecomp
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hnleReal : (n : ℝ) ≤ C * (D + 1) := by exact_mod_cast hnle
    have hCle : (C : ℝ) ≤ C * D := by
      nlinarith [mul_le_mul_of_nonneg_left hDreal (show (0 : ℝ) ≤ C by positivity)]
    nlinarith
  have hmanyreal :
      (#(denseGrids (δ / 2) m n D A) : ℝ) ≤
        #(containedProgressions k n A) * (m : ℝ) ^ 2 := by
    exact_mod_cast hmany
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hCreal : (0 : ℝ) < C := by exact_mod_cast hC
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hgood' :
      δ * n * D ≤ 4 * (#(denseGrids (δ / 2) m n D A) : ℝ) := by
    nlinarith
  have hgoodAP :
      δ * n * D ≤ 4 * ((#(containedProgressions k n A) : ℝ) * m ^ 2) :=
    hgood'.trans (mul_le_mul_of_nonneg_left hmanyreal (by norm_num))
  have htarget :
      δ * n ^ 2 ≤ 8 * C * m ^ 2 * (#(containedProgressions k n A) : ℝ) := by
    calc
      δ * n ^ 2 ≤ δ * n * (2 * C * D) := by
        have := mul_le_mul_of_nonneg_left hnCD
          (mul_nonneg hδ.le (show (0 : ℝ) ≤ n by positivity))
        nlinarith
      _ = 2 * C * (δ * n * D) := by ring
      _ ≤ 2 * C * (4 * (#(containedProgressions k n A) : ℝ) * m ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [mul_assoc] using hgoodAP
        · positivity
      _ = 8 * C * m ^ 2 * (#(containedProgressions k n A) : ℝ) := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀]
  · nlinarith [htarget]
  · positivity

end Combinatorics.ArithmeticProgression

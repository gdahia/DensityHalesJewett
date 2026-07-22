/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.DensityIncrement
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination

/-!
# Density Hales--Jewett

The binary base case and induction on the alphabet size.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Identify a binary word with the coordinates on which it equals `1`. -/
def binarySupport {ι : Type*} [Fintype ι] (w : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i ↦ w i = 1

/-- Two binary words are the ordered points of a combinatorial line exactly when their supports
are strictly comparable. -/
lemma binary_line_iff_ssubset {ι : Type*} [Fintype ι] (x y : ι → Fin 2) :
    (∃ l : Combinatorics.Line (Fin 2) ι, l 0 = x ∧ l 1 = y) ↔
      binarySupport x ⊂ binarySupport y := by
  constructor
  · rintro ⟨l, hlx, hly⟩
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ?_
    · intro i hix
      rw [← hlx] at hix
      rw [← hly]
      simp only [binarySupport, mem_filter, mem_univ, true_and] at hix ⊢
      change (l.idxFun i).getD 0 = 1 at hix
      change (l.idxFun i).getD 1 = 1
      cases hi : l.idxFun i
      · exfalso
        rw [hi] at hix
        exact Fin.zero_ne_one hix
      · rw [hi] at hix
        exact hix
    · obtain ⟨i, hi⟩ := l.proper
      refine ⟨i, ?_, ?_⟩
      · rw [← hly]
        simp only [binarySupport, mem_filter, mem_univ, true_and]
        change (l.idxFun i).getD 1 = 1
        rw [hi]
        simp
      · rw [← hlx]
        simp only [binarySupport, mem_filter, mem_univ, true_and]
        change ¬ (l.idxFun i).getD 0 = 1
        rw [hi]
        simp
  · classical
    intro h
    obtain ⟨i, hiy, hix⟩ := (Finset.ssubset_iff_of_subset h.1).1 h
    have hyi : y i = 1 := by
      simpa [binarySupport] using hiy
    have hxi₀ : x i = 0 := by
      obtain hxi₀ | ⟨j, hxi₀⟩ := (x i).eq_zero_or_eq_succ
      · exact hxi₀
      · rw [Fin.eq_zero j] at hxi₀
        exfalso
        apply hix
        simp only [binarySupport, mem_filter, mem_univ, true_and]
        exact hxi₀
    let l : Combinatorics.Line (Fin 2) ι :=
      ⟨fun j ↦ if x j = 0 ∧ y j = 1 then none else some (x j), ⟨i, by simp [hxi₀, hyi]⟩⟩
    refine ⟨l, ?_, ?_⟩
    · funext j
      simp only [l, Combinatorics.Line.coe_apply]
      split
      · rename_i hj
        simp [hj.1]
      · simp
    · funext j
      simp only [l, Combinatorics.Line.coe_apply]
      split
      · rename_i hj
        simp [hj.2]
      · rename_i hj
        simp only [Option.getD_some]
        obtain hxj | ⟨a, hxj⟩ := (x j).eq_zero_or_eq_succ
        · obtain hyj | ⟨b, hyj⟩ := (y j).eq_zero_or_eq_succ
          · rw [hxj, hyj]
          · rw [Fin.eq_zero b] at hyj
            exact (hj ⟨hxj, hyj⟩).elim
        · rw [Fin.eq_zero a] at hxj
          rw [hxj]
          symm
          change y j = 1
          suffices j ∈ binarySupport y by
            simpa only [binarySupport, mem_filter, mem_univ, true_and] using this
          apply h.1
          simp only [binarySupport, mem_filter, mem_univ, true_and]
          exact hxj

/-- Binary support faithfully records a binary word. -/
lemma binarySupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (binarySupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  apply Fin.ext
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [binarySupport, mem_filter, mem_univ, true_and] using Finset.ext_iff.mp hxy i
  grind

/-- A squared elementary upper bound for the normalized central binomial coefficient. -/
lemma centralBinom_ratio_sq_mul_le (m : ℕ) :
    ((Nat.centralBinom m : ℝ) / 4 ^ m) ^ 2 * (3 * m + 1) ≤ 1 := by
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec : ((m + 1 : ℕ) : ℝ) * Nat.centralBinom (m + 1) =
          2 * (2 * m + 1) * Nat.centralBinom m := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hratio : (Nat.centralBinom (m + 1) : ℝ) / 4 ^ (m + 1) =
          ((Nat.centralBinom m : ℝ) / 4 ^ m) *
            ((2 * m + 1 : ℝ) / (2 * (m + 1))) := by
        rw [pow_succ]
        field_simp
        push_cast at hrec ⊢
        linear_combination 2 * hrec
      rw [hratio, mul_pow, mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) ih
      rw [div_pow, div_mul_eq_mul_div]
      refine (div_le_iff₀ (sq_pos_of_pos (by positivity))).mpr ?_
      push_cast
      ring_nf
      nlinarith

/-- The middle binomial coefficient is at most the reciprocal square-root proportion of the
Boolean cube. -/
lemma centralBinom_ratio_le_inv_sqrt (m : ℕ) :
    (Nat.centralBinom m : ℝ) / 4 ^ m ≤ (√(3 * m + 1))⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [one_pow] using centralBinom_ratio_sq_mul_le m

/-- Reduce the normalized middle binomial coefficient in any dimension to the central coefficient
in half that dimension. -/
lemma middleBinomial_ratio_le_central (n : ℕ) :
    (n.choose (n / 2) : ℝ) / 2 ^ n ≤
      (Nat.centralBinom (n / 2) : ℝ) / 4 ^ (n / 2) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    have hdiv : 2 * m / 2 = m := by grind
    rw [hdiv, Nat.centralBinom]
    rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]]
  · subst n
    have hdiv : (2 * m + 1) / 2 = m := by grind
    rw [hdiv, Nat.centralBinom]
    cases m with
    | zero => norm_num
    | succ m =>
      have hchoose : (2 * (m + 1) + 1).choose (m + 1) ≤
          2 * Nat.centralBinom (m + 1) := by
        rw [Nat.choose_succ_left (2 * (m + 1)) (m + 1) (by grind)]
        simpa only [Nat.add_sub_cancel, two_mul] using
          add_le_add (Nat.choose_le_centralBinom m (m + 1))
            (Nat.choose_le_centralBinom (m + 1) (m + 1))
      rw [pow_succ, show (2 : ℝ) ^ (2 * (m + 1)) = 4 ^ (m + 1) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]]
      rw [mul_comm (4 ^ (m + 1) : ℝ) 2]
      refine le_trans (b := (2 * Nat.centralBinom (m + 1) : ℝ) /
        (2 * 4 ^ (m + 1))) ?_ ?_
      · exact (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 2 * 4 ^ (m + 1))).mpr <| by
            exact_mod_cast hchoose
      · field_simp
        rfl

/-- Eventually the middle layer occupies less than any prescribed positive proportion of the
Boolean cube. -/
lemma exists_middleBinomial_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → (n.choose (n / 2) : ℝ) < δ * 2 ^ n := by
  have ht : Filter.Tendsto (fun m : ℕ ↦ (√(3 * (m : ℝ) + 1))⁻¹)
      Filter.atTop (nhds 0) := by
    refine tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ?_)
    simpa only [add_comm] using
      tendsto_const_nhds.add_atTop
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ))
          Filter.atTop Filter.atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hδ)
  refine ⟨2 * M, ?_⟩
  intro n hn
  have hMn : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by grind)
  refine (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp ?_
  refine (middleBinomial_ratio_le_central n).trans_lt <|
    (centralBinom_ratio_le_inv_sqrt (n / 2)).trans_lt ?_
  exact hM (n / 2) hMn

/-- Density Hales--Jewett for the binary alphabet. -/
lemma dhj_two : HasDensityHJ 2 := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_middleBinomial_lt δ hδ
  refine ⟨N, ?_⟩
  intro n hn A hA
  by_contra hline
  let B := A.image binarySupport
  have hB : IsAntichain (· ⊆ ·) (B : Set (Finset (Fin n))) := by
    intro s hs t ht hst hsub
    change s ∈ B at hs
    change t ∈ B at ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    apply hline
    obtain ⟨l, hlx, hly⟩ := (binary_line_iff_ssubset x y).2 <|
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, hst⟩
    refine ⟨l, ?_⟩
    intro a
    obtain rfl | ⟨i, rfl⟩ := a.eq_zero_or_eq_succ
    · rw [hlx]
      exact hx
    · simp only [Fin.eq_zero i]
      change l 1 ∈ A
      rw [hly]
      exact hy
  have hcard : #A ≤ n.choose (n / 2) := by
    rw [← Finset.card_image_of_injective A binarySupport_injective]
    simpa only [B, Fintype.card_fin] using hB.sperner
  exact (not_lt_of_ge (hA.trans <| by exact_mod_cast hcard)) (hN n hn)

/-- **Easy helper:** a positive uniform increment eventually raises the density floor above one. -/
lemma exists_density_increment_steps {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 1 < δ + (R : ℝ) * (Parameters.γ k δ / 2) := by
  sorry

/-- **Medium helper:** choose the dimensions for a finite density-increment iteration backwards.

The last parameter cube has dimension one.  At stage `j`, the preceding dimension is large enough
to apply `density_increment` with density floor `δ + j * (γ k δ / 2)` and target dimension
`d (j + 1)`. -/
lemma exists_density_increment_schedule (k R : ℕ) (δ : ℝ) :
    ∃ d : ℕ → ℕ,
      d R = 1 ∧
      (∀ j, j ≤ R → 1 ≤ d j) ∧
      ∀ j, j < R →
        incrementBound k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j := by
  sorry

/-- **Hard helper:** iterate the density-increment dichotomy along a backward dimension schedule.

Pull back the family after each increment and compose the resulting nested subspaces.  A line in
any parameter cube gives a line in the original family.  Otherwise monotonicity of `Parameters.γ`
raises the density by at least `Parameters.γ k δ / 2` at every stage, and the final relative
density is at most one. -/
lemma line_or_iterated_density_le_one {k R n : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    {δ : ℝ} (hδ : 0 < δ) (d : ℕ → ℕ)
    (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R →
      incrementBound k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (hn : d 0 ≤ n) (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤ 1 := by
  sorry

/-- Density Hales--Jewett for every finite alphabet of cardinality at least two. -/
lemma density_hales_jewett_fin (k : ℕ) (hk : 2 ≤ k) : HasDensityHJ k := by
  induction k, hk using Nat.le_induction with
  | base => exact dhj_two
  | succ k hk hDHJ =>
      intro δ hδ
      obtain ⟨R, hR⟩ := exists_density_increment_steps hk hδ
      obtain ⟨d, _, hd, hstep⟩ := exists_density_increment_schedule k R δ
      refine ⟨d 0, ?_⟩
      intro n hn A hA
      refine (line_or_iterated_density_le_one hk hDHJ hδ d hd hstep hn A ?_).resolve_right ?_
      · exact Subspace.density_le_of_card_le (Nat.zero_lt_succ k) δ A hA
      · exact not_le_of_gt hR

end DensityHalesJewett

namespace Combinatorics.Line

/-- A threshold for the density Hales--Jewett theorem over an alphabet of size `k`. -/
noncomputable def densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ :=
  if 2 ≤ k then DensityHalesJewett.Subspace.densityOneBound k δ else 1

/-- The density theorem for alphabets with at most one letter. -/
lemma exists_of_density_card_le_one (α : Type*) [Fintype α]
    (hα : Fintype.card α ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin n → α))
    (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  letI : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hα
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨Line.diagonal α (Fin n), ?_⟩
  intro x
  have hcard : Fintype.card α = 1 :=
    Fintype.card_eq_one_of_forall_eq fun y ↦ Subsingleton.elim y x
  rw [hcard] at hAδ
  norm_num at hAδ
  obtain ⟨w, hw⟩ : A.Nonempty := Finset.card_pos.mp <| by
    exact_mod_cast hδ.trans_le hAδ
  simpa only [Subsingleton.elim (Line.diagonal α (Fin n) x) w] using hw

/-- Transport the finite-alphabet density theorem across the canonical alphabet equivalence. -/
lemma exists_of_density_card_ge_two (α : Type*) [Fintype α]
    (hα : 2 ≤ Fintype.card α) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : DensityHalesJewett.Subspace.densityOneBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let e := Fintype.equivFin α
  let wordEquiv : (Fin n → α) ≃ (Fin n → Fin (Fintype.card α)) :=
    (Equiv.refl (Fin n)).arrowCongr e
  let B := A.map wordEquiv.toEmbedding
  have hB : δ * (Fintype.card α : ℝ) ^ n ≤ #B := by
    simpa only [B, Finset.card_map] using hAδ
  obtain ⟨l, hl⟩ := DensityHalesJewett.Subspace.densityOneBound_spec
    (DensityHalesJewett.density_hales_jewett_fin (Fintype.card α) hα)
    δ hδ n hn B hB
  refine ⟨l.map e.symm, ?_⟩
  intro x
  specialize hl (e x)
  rw [Finset.mem_map_equiv] at hl
  change (e.symm ∘ l (e x)) ∈ A at hl
  rw [← e.symm_apply_apply x, Combinatorics.Line.map_apply]
  exact hl

lemma densityTheoremBound_spec (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  by_cases hα : 2 ≤ Fintype.card α
  · refine exists_of_density_card_ge_two α hα δ hδ n ?_ A hAδ
    simpa only [densityTheoremBound, if_pos hα] using hn
  · refine exists_of_density_card_le_one α (by grind) δ hδ n ?_ A hAδ
    simpa only [densityTheoremBound, if_neg hα] using hn

theorem exists_of_density (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  exact densityTheoremBound_spec α δ hδ n hn A hAδ

end Combinatorics.Line

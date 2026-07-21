/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.DensityIncrement
public import Mathlib.Combinatorics.SetFamily.LYM

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
theorem binary_line_iff_ssubset {ι : Type*} [Fintype ι] (x y : ι → Fin 2) :
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

/-- Density Hales--Jewett for the binary alphabet. -/
theorem dhj_two : HasDensityHJ 2 := by
  sorry

/-- Density Hales--Jewett for every finite alphabet of cardinality at least two. -/
theorem density_hales_jewett_fin (k : ℕ) (hk : 2 ≤ k) : HasDensityHJ k := by
  sorry

end DensityHalesJewett

namespace Combinatorics.Line

/-- A threshold for the density Hales--Jewett theorem over an alphabet of size `k`. -/
opaque densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ

theorem exists_of_density (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  sorry

end Combinatorics.Line

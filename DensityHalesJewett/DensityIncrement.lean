/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Insensitive
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The density-increment dichotomy

Numerical parameters, correlated fibers, structured correlation, and the density increment
proposition.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

namespace Parameters

/-- A positive dimension selected from the density Hales--Jewett assertion when available. -/
noncomputable def m₀ (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.succ <| Nat.find <| h.2 (δ / 4) (by linarith)
  else 1

lemma m₀_pos (k : ℕ) (δ : ℝ) : 0 < m₀ k δ := by
  classical
  unfold m₀
  split <;> simp

/-- The selected dimension is antitone in the density threshold. -/
lemma m₀_antitone {k : ℕ} (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : m₀ k ρ ≤ m₀ k δ := by
  classical
  rw [m₀, dif_pos ⟨hδ.trans_le hδρ, hDHJ⟩, m₀, dif_pos ⟨hδ, hDHJ⟩]
  apply Nat.succ_le_succ
  apply Nat.find_min'
  intro n hn A hA
  refine Nat.find_spec (hDHJ (δ / 4) (by linarith)) n hn A (le_trans (by gcongr) hA)

/-- The denominator in the parameter definition grows with the selected dimension. -/
lemma power_difference_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m ≤
      ((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    refine ih.trans ?_
    rw [Nat.cast_add, Nat.cast_one]
    suffices 0 ≤ (k : ℝ) * (((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n) by
      rw [Nat.cast_add, Nat.cast_one] at this
      nlinarith [pow_nonneg (by positivity : 0 ≤ (k : ℝ)) n]
    apply mul_nonneg
    · positivity
    · apply sub_nonneg.mpr
      apply pow_le_pow_left₀
      · positivity
      · exact_mod_cast Nat.le_succ k

/-- The denominator defining `θ` is positive for every admissible alphabet and density. -/
lemma θ_denominator_pos {k : ℕ} (hk : 2 ≤ k) (δ : ℝ) :
    0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
  apply sub_pos.mpr
  apply pow_lt_pow_left₀
  · exact_mod_cast Nat.lt_succ_self k
  · positivity
  · exact Nat.ne_of_gt <| m₀_pos k δ

/-- The correlated-fibers threshold attached to an alphabet size and density. -/
noncomputable def θ (k : ℕ) (δ : ℝ) : ℝ :=
  (δ / 4) /
    (((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ)

/-- The threshold is monotone in the density parameter. -/
lemma θ_mono_of_dhj {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  unfold θ
  refine div_le_div₀ ?_ (by linarith) (θ_denominator_pos hk ρ) ?_
  · exact div_nonneg (hδ.trans_le hδρ).le (by norm_num)
  · exact power_difference_mono k <| m₀_antitone hDHJ hδ hδρ

/-- The threshold is monotone even when the density Hales--Jewett assertion is unavailable. -/
lemma θ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  classical
  by_cases hDHJ : HasDensityHJ k
  · exact θ_mono_of_dhj hk hDHJ hδ hδρ
  · unfold θ
    rw [m₀, dif_neg (fun h ↦ hDHJ h.2), m₀, dif_neg (fun h ↦ hDHJ h.2)]
    apply div_le_div_of_nonneg_right
    · linarith
    · rw [pow_one, pow_one, Nat.cast_add, Nat.cast_one]
      linarith

lemma θ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < θ k δ := by
  unfold θ
  exact div_pos (by positivity) (θ_denominator_pos hk δ)

/-- The error tolerance attached to an alphabet size and density. -/
noncomputable def η (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))

/-- The error tolerance is monotone in the density parameter. -/
lemma η_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : η k δ ≤ η k ρ := by
  unfold η
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ (θ_mono hk hδ hδρ) (θ_pos hk hδ).le
        (hδ.trans_le hδρ).le
    · norm_num
  · exact div_le_div_of_nonneg_right (θ_mono hk hδ hδρ) (by norm_num)
  · exact div_le_div_of_nonneg_right hδρ (by norm_num)

lemma η_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < η k δ := by
  unfold η
  apply lt_min
  · positivity [θ_pos hk hδ]
  · apply lt_min
    · positivity [θ_pos hk hδ]
    · positivity

/-- The density increment attached to an alphabet size and density. -/
noncomputable def γ (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * η k δ ^ 2 / k) (min (η k δ ^ 2 / 2) (3 * η k δ))

/-- The increment is monotone in the density parameter. -/
lemma γ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : γ k δ ≤ γ k ρ := by
  unfold γ
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · apply mul_le_mul hδρ
      · exact (sq_le_sq₀ (η_pos hk hδ).le
          (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
      · positivity
      · exact (hδ.trans_le hδρ).le
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact (sq_le_sq₀ (η_pos hk hδ).le
        (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
    · norm_num
  · exact mul_le_mul_of_nonneg_left (η_mono hk hδ hδρ) (by norm_num)

lemma γ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < γ k δ := by
  unfold γ
  positivity [η_pos hk hδ]

lemma η_lt_θ_div_two {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    η k δ < θ k δ / 2 := by
  unfold η
  refine lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) ?_
  linarith [θ_pos hk hδ]

lemma η_le_δ_div_six (k : ℕ) (δ : ℝ) : η k δ ≤ δ / 6 := by
  unfold η
  exact (min_le_right _ _).trans (min_le_right _ _)

lemma γ_le_η_sq_div_two (k : ℕ) (δ : ℝ) : γ k δ ≤ η k δ ^ 2 / 2 := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma γ_le_three_mul_η (k : ℕ) (δ : ℝ) : γ k δ ≤ 3 * η k δ := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The increment parameters can be chosen uniformly above a fixed positive density floor. -/
lemma γ_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < γ k δ₀ ∧ ∀ ρ, δ₀ ≤ ρ → γ k δ₀ ≤ γ k ρ := by
  refine ⟨γ_pos hk hδ₀, ?_⟩
  intro ρ hδρ
  exact γ_mono hk hδ₀ hδρ

end Parameters

/-- A finite word family contains no complete combinatorial line. -/
def IsLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A

/-- Pull a word family back to the parameter cube of a subspace. -/
def pullback {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι → α)) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ V x ∈ A

/-- A bound for the correlated-fibers lemma. -/
noncomputable def correlatedFibersBound (k m : ℕ) (δ : ℝ) : ℕ :=
  let M := max m (Parameters.m₀ k δ)
  let L := GrahamRothschild.bound (k + 1) 2 M
  Subspace.uniformFibersBound (k + 1) L (Parameters.η k δ ^ 2 / 2)

/-- The correlated-fibers bound leaves room first for uniformizing fibers and then for canonizing
the resulting two-coloring of parameter lines. -/
lemma correlatedFibersBound_spec {k : ℕ} (_hk : 2 ≤ k) (_hDHJ : HasDensityHJ k)
    (m : ℕ) (_hm : 1 ≤ m) {δ : ℝ} (_hδ₀ : 0 < δ) (_hδ₁ : δ ≤ 1)
    {ι : Type*} [Fintype ι]
    (hι : correlatedFibersBound k m δ ≤ Fintype.card ι) :
    ∃ M L : ℕ,
      m ≤ M ∧ Parameters.m₀ k δ ≤ M ∧
      GrahamRothschild.bound (k + 1) 2 M ≤ L ∧
      Subspace.uniformFibersBound (k + 1) L (Parameters.η k δ ^ 2 / 2) ≤
        Fintype.card ι := by
  refine ⟨max m (Parameters.m₀ k δ),
    GrahamRothschild.bound (k + 1) 2 (max m (Parameters.m₀ k δ)),
    le_max_left _ _, le_max_right _ _, le_rfl, ?_⟩
  simpa only [correlatedFibersBound] using hι

/-- Uniformization followed by line canonization produces a large subspace on which every
restricted-alphabet line is uniformly good or uniformly sparse. -/
lemma exists_uniform_fibers_and_homogeneous_lines {k M L : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (huniform :
      Subspace.uniformFibersBound (k + 1) L (Parameters.η k δ ^ 2 / 2) ≤
        Fintype.card ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
      ((∀ l : Combinatorics.Line (Fin k) (Fin M),
          Parameters.θ k δ ≤
            ((Finset.univ.filter fun y ↦
              ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
        (∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ)) := by
  letI : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ε := Parameters.η k δ ^ 2 / 2
  have hε₀ : 0 < ε := by
    dsimp only [ε]
    positivity [Parameters.η_pos hk hδ₀]
  have hεδ : ε < δ := by
    dsimp only [ε]
    have hdiff : 0 ≤ δ / 6 - Parameters.η k δ := by
      linarith [Parameters.η_le_δ_div_six k δ]
    have hsum : 0 ≤ δ / 6 + Parameters.η k δ := by
      linarith [Parameters.η_pos hk hδ₀]
    nlinarith [mul_nonneg hdiff hsum]
  have hε₁ : ε < 1 := hεδ.trans_le hδ₁
  by_cases hM : 1 ≤ M
  · have hL : 1 ≤ L := by
      by_contra hL
      have hL₀ : L = 0 := by omega
      subst L
      obtain ⟨R, _⟩ :=
        GrahamRothschild.lines_twoColor (Fin (k + 1)) M 0 hM
          (by simpa only [Fintype.card_fin] using hGR) ∅
      obtain ⟨i, _⟩ := R.proper ⟨0, hM⟩
      exact Fin.elim0 i
    obtain ⟨U, hU⟩ :=
      Subspace.exists_fibers_dense (α := Fin (k + 1)) (ι := ι) (κ := κ)
        L hL ε hε₀ hε₁ (by simpa only [Fintype.card_fin, ε] using huniform)
        A (hεδ.trans_le hA)
    letI : Fintype (Combinatorics.Line (Fin (k + 1)) (Fin L)) :=
      Subspace.lineFintype (k + 1) L
    let goodLines :=
      Finset.univ.filter fun q : Combinatorics.Line (Fin (k + 1)) (Fin L) ↦
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a : Fin k, concat (U (q a.castSucc)) y ∈ A).dens : ℝ)
    obtain ⟨R, hgood | hbad⟩ :=
      GrahamRothschild.lines_twoColor (Fin (k + 1)) M L hM
        (by simpa only [Fintype.card_fin] using hGR) goodLines
    · refine ⟨Subspace.compose U R, ?_, Or.inl ?_⟩
      · intro x
        rw [Subspace.compose_apply]
        have hx := hU (R x)
        dsimp only [ε] at hx
        linarith
      · intro l
        have hl := hgood (l.map Fin.castSucc)
        simpa only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply,
          Subspace.compose_apply] using hl
    · refine ⟨Subspace.compose U R, ?_, Or.inr ?_⟩
      · intro x
        rw [Subspace.compose_apply]
        have hx := hU (R x)
        dsimp only [ε] at hx
        linarith
      · intro l
        have hl := hbad (l.map Fin.castSucc)
        simp only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply] at hl
        simpa only [Subspace.compose_apply] using lt_of_not_ge hl
  · have hM₀ : M = 0 := by omega
    subst M
    letI : Fintype (ι → Fin (k + 1)) := Fintype.ofFinite _
    have havg :
        δ ≤ 𝔼 x : ι → Fin (k + 1), ((fiber A x).dens : ℝ) := by
      simpa only [average_density_fiber] using hA
    obtain ⟨x, _, hx⟩ :=
      Finset.exists_le_of_le_expect Finset.univ_nonempty havg
    let W : Combinatorics.Subspace (Fin 0) (Fin (k + 1)) ι := {
      idxFun := fun i ↦ Sum.inl (x i)
      proper := fun e ↦ Fin.elim0 e
    }
    refine ⟨W, ?_, Or.inl ?_⟩
    · intro z
      have hW : W z = x := by
        funext i
        simp only [W, Combinatorics.Subspace.coe_apply, Sum.elim_inl, id_eq]
      rw [hW]
      dsimp only [ε] at hε₀
      linarith
    · intro l
      exact Fin.elim0 l.proper.choose

/-- Restricting the parameter directions of a good correlated-fibers subspace preserves its
uniform fiber and common-line-fiber estimates. -/
lemma restrict_correlated_fibers_subspace {k m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M)
    {δ : ℝ} {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  let R := Subspace.repeatInitial (Fin (k + 1)) hm hmM
  let V := Subspace.compose W R
  refine ⟨V, ?_, ?_⟩
  · intro x
    dsimp only [V]
    rw [Subspace.compose_apply]
    exact hfibers (R x)
  · intro l
    let Rk := Subspace.repeatInitial (Fin k) hm hmM
    simpa only [V, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using
        hlines (Subspace.composeLine Rk l)

/-- Uniformize the fibers and canonize their line-density coloring.

The working parameter dimension is chosen large enough both for the requested `m`-dimensional
output and for the density Hales--Jewett argument at dimension `Parameters.m₀ k δ`.  In the
monochromatic good case, restrict the working subspace to `m` parameters.  In the bad case, retain
the larger subspace as a certificate whose every restricted-alphabet line has common-suffix density
strictly below `Parameters.θ k δ`. -/
lemma exists_correlated_fibers_or_sparse_certificate {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hι : correlatedFibersBound k m δ ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
      ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
        ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
          (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin M),
            ((Finset.univ.filter fun y ↦
              ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
                Parameters.θ k δ := by
  obtain ⟨M, L, hmM, hm₀M, hGR, huniform⟩ :=
    correlatedFibersBound_spec hk hDHJ m hm hδ₀ hδ₁ hι
  obtain ⟨W, hfibers, hgood | hsparse⟩ :=
    exists_uniform_fibers_and_homogeneous_lines hk hδ₀ hδ₁ hGR huniform A hA
  · exact Or.inl <|
      restrict_correlated_fibers_subspace hm hmM A W hfibers hgood
  · exact Or.inr ⟨M, hm₀M, W, hfibers, hsparse⟩

/-- Uniformly dense fibers force a positive-density set of suffixes whose restricted parameter
slice has density at least `δ / 4`. -/
lemma dense_suffixes_of_uniform_fibers {k M : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    δ / 4 ≤
      ((Finset.univ.filter fun y : κ → Fin (k + 1) ↦
        δ / 4 ≤
          ((Finset.univ.filter fun x : Fin M → Fin k ↦
            concat (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)).dens : ℝ) := by
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let f := fun y : κ → Fin (k + 1) ↦
    ((Finset.univ.filter fun x : Fin M → Fin k ↦
      concat (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hη₀ := Parameters.η_pos hk hδ₀
  have hηδ := Parameters.η_le_δ_div_six k δ
  have hηsq : Parameters.η k δ ^ 2 ≤ (δ / 6) ^ 2 :=
    (sq_le_sq₀ hη₀.le (by positivity)).mpr hηδ
  have havg : δ - Parameters.η k δ ^ 2 / 2 ≤
      Finset.expect Finset.univ f := by
    rw [Subspace.average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty fun x _ ↦
      hfibers (Fin.castSucc ∘ x)
  have hthreshold := density_ge_threshold f
    (δ - Parameters.η k δ ^ 2 / 2) (δ / 4)
    (fun y ↦ by
      dsimp only [f]
      positivity)
    (fun y ↦ by
      dsimp only [f]
      exact_mod_cast Finset.dens_le_one)
    (by positivity) (by nlinarith [sq_nonneg δ]) havg
  refine (le_div_iff₀ (by linarith : 0 < 1 - δ / 4)).mpr ?_ |>.trans hthreshold
  nlinarith [sq_nonneg δ]

/-- Density Hales--Jewett in every dense suffix slice, followed by finite pigeonhole, produces
one parameter line shared by at least a `θ`-density set of suffixes. -/
lemma exists_popular_line_of_dense_suffixes {k M : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hM : Parameters.m₀ k δ ≤ M)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  classical
  let q := Parameters.m₀ k δ
  have hq₀ : 0 < q := Parameters.m₀_pos k δ
  let R := Subspace.repeatInitial (Fin (k + 1)) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  let W₀ := Subspace.compose W R
  have hW₀ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W₀ x)).dens : ℝ) := by
    intro x
    simpa only [W₀, Subspace.compose_apply] using hfibers (R x)
  have hdense := dense_suffixes_of_uniform_fibers hk hδ₀ hδ₁ A W₀ hW₀
  letI := Subspace.lineFintype k q
  let B := Finset.univ.filter fun y : κ → Fin (k + 1) ↦
    δ / 4 ≤
      ((Finset.univ.filter fun x : Fin q → Fin k ↦
        concat (W₀ (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hB : δ / 4 ≤ (B.dens : ℝ) := by
    simpa only [B] using hdense
  have hBne : B.Nonempty := by
    apply Finset.dens_pos.mp
    exact_mod_cast lt_of_lt_of_le (by linarith : 0 < δ / 4) hB
  have hbound : Subspace.densityOneBound k (δ / 4) ≤ q := by
    dsimp only [q]
    rw [Subspace.densityOneBound, dif_pos ⟨by linarith, hDHJ⟩,
      Parameters.m₀, dif_pos ⟨hδ₀, hDHJ⟩]
    omega
  have existsLine (y : κ → Fin (k + 1)) (hy : y ∈ B) :
      ∃ l : Combinatorics.Line (Fin k) (Fin q),
        ∀ a, concat (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    let S := Finset.univ.filter fun x : Fin q → Fin k ↦
      concat (W₀ (Fin.castSucc ∘ x)) y ∈ A
    obtain ⟨l, hl⟩ :=
      Subspace.densityOneBound_spec hDHJ (δ / 4) (by linarith) q hbound S <|
        Subspace.card_le_of_density_le (by omega) (δ / 4) S
          (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, S] using hy)
    exact ⟨l, fun a ↦ by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hl a⟩
  let y₀ := hBne.choose
  have hy₀ : y₀ ∈ B := hBne.choose_spec
  obtain ⟨l₀, _⟩ := existsLine y₀ hy₀
  letI : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let lineAt : {y // y ∈ B} → Combinatorics.Line (Fin k) (Fin q) := fun y ↦
    Classical.choose <| existsLine y y.2
  let f : (κ → Fin (k + 1)) → Combinatorics.Line (Fin k) (Fin q) := fun y ↦
    if hy : y ∈ B then lineAt ⟨y, hy⟩ else l₀
  obtain ⟨l, hl⟩ := Subspace.exists_fiber_density B f
  have hcommon :
      (B.filter fun y ↦ f y = l) ⊆
        Finset.univ.filter fun y ↦
          ∀ a, concat (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hline : lineAt ⟨y, hy.1⟩ = l := by
      simpa only [f, dif_pos hy.1] using hy.2
    intro a
    rw [← hline]
    exact Classical.choose_spec (existsLine y hy.1) a
  have hcard :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ q - (k : ℝ) ^ q := by
    rw [Subspace.card_line k q (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) q
  have hθ :
      Parameters.θ k δ ≤
        (B.dens : ℝ) / Fintype.card (Combinatorics.Line (Fin k) (Fin q)) := by
    unfold Parameters.θ
    rw [← hcard]
    exact div_le_div_of_nonneg_right hB (by positivity)
  let Rk := Subspace.repeatInitial (Fin k) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  refine ⟨Subspace.composeLine Rk l, hθ.trans (hl.trans ?_)⟩
  exact_mod_cast Finset.dens_le_dens <| by
    simpa only [W₀, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using hcommon

/-- The uniformly sparse certificate is impossible.

Average the dense fibers over suffixes, find many suffix slices of density at least `δ / 4`, and
apply `hDHJ` on an embedded `Parameters.m₀ k δ`-dimensional parameter cube in each such slice.
Pigeonholing the resulting lines gives one line with common-suffix density at least
`Parameters.θ k δ`, contradicting the certificate. -/
lemma not_exists_sparse_correlated_fibers_certificate {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    ¬ ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
      ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
        (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
        ∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ := by
  rintro ⟨M, hM, W, hfibers, hsparse⟩
  obtain ⟨l, hl⟩ :=
    exists_popular_line_of_dense_suffixes hk hDHJ hδ₀ hδ₁ hM A W hfibers
  exact (not_lt_of_ge hl) (hsparse l)

/-- Every parameter-cube line in a suitable subspace has a dense common fiber. -/
lemma exists_subspace_correlated_fibers {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hι : correlatedFibersBound k m δ ≤ Fintype.card ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦ ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  obtain hV | hsparse :=
    exists_correlated_fibers_or_sparse_certificate hk hDHJ m hm δ hδ₀ hδ₁ hι A hA
  · exact hV
  · exact (not_exists_sparse_correlated_fibers_certificate hk hDHJ δ hδ₀ hδ₁ A
      hsparse).elim

/-- The pullback of a word family to a subspace after fixing the suffix coordinates. -/
def suffixPullback {α η ι κ : Type*} [Fintype (η → α)]
    [DecidableEq (ι ⊕ κ → α)] (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι ⊕ κ → α)) (y : κ → α) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ concat (V x) y ∈ A

/-- The parameter lines whose first-`k` points belong to a word family at a fixed suffix. -/
def suffixLines {k m : ℕ} {ι κ : Type*}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (y : κ → Fin (k + 1)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter fun l ↦ ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A

/-- Fix suffix coordinates of a subspace. -/
def Subspace.fixSuffix {α η ι κ : Type*} (V : Combinatorics.Subspace η α ι)
    (y : κ → α) : Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun := Sum.elim V.idxFun (Sum.inl ∘ y)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

/-- Fix suffix coordinates and transport the ambient coordinates along an equivalence. -/
def Subspace.fixSuffixReindex {α η ι κ ζ : Type*} (e : ι ⊕ κ ≃ ζ)
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α ζ :=
  (Subspace.fixSuffix V y).reindex (Equiv.refl _) (Equiv.refl _) e

/-- Pointwise fiber lower bounds imply the corresponding average lower bound for fixed-suffix
pullbacks.  This is a finite double-counting argument. -/
lemma average_suffixPullback_lower {α η ι κ : Type*} [Nonempty α] [Fintype (η → α)]
    [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) (r : ℝ)
    (hV : ∀ x, r ≤ ((fiber A (V x)).dens : ℝ)) :
    r ≤ 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) =
      𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
    calc
      𝔼 x : η → α, ((fiber A (V x)).dens : ℝ)
          = 𝔼 x : η → α, 𝔼 y : κ → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        simp
      _ = 𝔼 y : κ → α, 𝔼 x : η → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (η → α)) (Finset.univ : Finset (κ → α))]
      _ = 𝔼 y : κ → α, 𝔼 x : η → α,
          (Set.indicator (suffixPullback V A y) (1 : (η → α) → ℝ) x : ℝ) := by
        refine Finset.expect_congr rfl fun y _ => ?_
        refine Finset.expect_congr rfl fun x _ => ?_
        by_cases h : concat (V x) y ∈ A
        · have hy : y ∈ fiber A (V x) := by simpa [fiber] using h
          have hx : x ∈ suffixPullback V A y := by
            dsimp [suffixPullback]
            simp [h]
          simp [hy, hx]
        · have hy : y ∉ fiber A (V x) := by simpa [fiber] using h
          have hx : x ∉ suffixPullback V A y := by
            dsimp [suffixPullback]
            simp [h]
          simp [hy, hx]
      _ = 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
        simp
  have h_r_le_expect : r ≤ 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := η → α)) fun x _ => hV x
  exact h_r_le_expect.trans h_expect_eq.le

/-- If a bounded function has average at least `δ - η²/2` but never reaches
`δ + η²/2`, then it is at least `δ - 2η` on all but an `η`-fraction of its domain. -/
lemma density_near_average {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (δ η : ℝ) (hη₀ : 0 < η) (_hη₁ : η ≤ 1)
    (_hf₀ : ∀ x, 0 ≤ f x) (_hf₁ : ∀ x, f x ≤ 1)
    (havg : δ - η ^ 2 / 2 ≤ 𝔼 x : X, f x)
    (hupper : ∀ x, f x < δ + η ^ 2 / 2) :
    1 - η ≤ ((Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x).dens : ℝ) := by
  set H := Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x
  by_cases hH : 1 - η ≤ (H.dens : ℝ)
  · exact hH
  · exfalso
    have h_dens_H_lt : (H.dens : ℝ) < 1 - η := by linarith
    have h_pos : 0 < η ^ 2 / 2 + 2 * η := by nlinarith
    have hfg : ∀ x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η)
        * (Set.indicator H (1 : X → ℝ) x : ℝ) := by
      intro x
      by_cases hxH : x ∈ H
      · have h_indicator : (Set.indicator H (1 : X → ℝ) x : ℝ) = 1 := by simp [hxH]
        simp [h_indicator]
        linarith [hupper x]
      · have hx_lt : f x < δ - 2 * η := by
          have : ¬(δ - 2 * η ≤ f x) := by simpa [H] using hxH
          linarith
        have h_indicator : (Set.indicator H (1 : X → ℝ) x : ℝ) = 0 := by simp [hxH]
        simp [h_indicator]
        linarith
    have h_expect_f_le_expect_g : 𝔼 x : X, f x ≤ 𝔼 x : X, ((δ - 2 * η : ℝ) + (η ^ 2 / 2 + 2 * η) *
        (Set.indicator H (1 : X → ℝ) x : ℝ)) :=
      Finset.expect_le_expect (fun x _ => hfg x)
    have h_expect_g : 𝔼 x : X, ((δ - 2 * η : ℝ) + (η ^ 2 / 2 + 2 * η) *
        (Set.indicator H (1 : X → ℝ) x : ℝ)) =
      (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by
      calc
        𝔼 x : X, ((δ - 2 * η : ℝ) + (η ^ 2 / 2 + 2 * η) * (Set.indicator H (1 : X → ℝ) x : ℝ)) =
          𝔼 x : X, (δ - 2 * η : ℝ) + 𝔼 x : X, ((η ^ 2 / 2 + 2 * η)
            * (Set.indicator H (1 : X → ℝ) x : ℝ)) := by
          rw [Finset.expect_add_distrib]
        _ = (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * 𝔼 x : X, (Set.indicator H (1 : X → ℝ) x : ℝ) := by
          rw [Finset.expect_const univ_nonempty, ← Finset.mul_expect]
        _ = (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by simp
    rw [h_expect_g] at h_expect_f_le_expect_g
    have h_upper_bound : (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) <
      (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * (1 - η) := by
      nlinarith
    nlinarith

/-- Dense common suffix fibers for every line give the same lower bound for the average
fixed-suffix line density.  This is the second finite double-counting step. -/
lemma average_suffixLines_lower {k m : ℕ} {ι κ : Type*}
    [Fintype (κ → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (θ : ℝ)
    (hV : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ ((Finset.univ.filter fun y ↦
        ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    θ ≤ 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) =
      𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
    calc
      𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          ((Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)
          = 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
            𝔼 y : κ → Fin (k + 1),
            (Set.indicator (Finset.univ.filter fun y ↦
              ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A)
              (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        refine Finset.expect_congr rfl fun l _ => ?_
        rw [← Finset.expect_indicator_one]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (Finset.univ.filter fun y ↦
            ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A)
            (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (Combinatorics.Line (Fin k) (Fin m)))
          (Finset.univ : Finset (κ → Fin (k + 1)))]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (suffixLines V A y)
            (1 : Combinatorics.Line (Fin k) (Fin m) → ℝ) l : ℝ) := by
        refine Finset.expect_congr rfl fun y _ => ?_
        refine Finset.expect_congr rfl fun l _ => ?_
        dsimp [suffixLines]
        by_cases h : ∀ a : Fin k, concat (V (Fin.castSucc ∘ l a)) y ∈ A
        · simp [h]
        · simp [h]
      _ = 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
        simp
  have h_θ_le_expect : θ ≤ 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := Combinatorics.Line (Fin k) (Fin m)))
      fun l _ => hV l
  exact h_θ_le_expect.trans h_expect_eq.le

/-- A `[0,1]`-valued function with average at least `θ` exceeds `θ/2` on a set of
density at least `θ/2`. -/
lemma density_half_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1)
    (havg : θ ≤ 𝔼 x : X, f x) :
    θ / 2 ≤ ((Finset.univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) := by
  have hθ2_nonneg : 0 ≤ θ / 2 := by positivity
  have h_ge_threshold : (θ - θ / 2) / (1 - θ / 2) ≤
      ((Finset.univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) :=
    density_ge_threshold f θ (θ / 2) hf₀ hf₁ hθ2_nonneg (by linarith) havg
  have h_simplify : (θ - θ / 2) / (1 - θ / 2) = (θ / 2) / (1 - θ / 2) := by
    have hnum : θ - θ / 2 = θ / 2 := by ring
    rw [hnum]
  rw [h_simplify] at h_ge_threshold
  have h_half_le_div : θ / 2 ≤ (θ / 2) / (1 - θ / 2) := by
    have hpos : 0 < 1 - θ / 2 := by linarith
    rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg (θ / 2)]
  linarith

/-- Two subsets of densities at least `1-η` and `θ/2` intersect when `η < θ/2`. -/
lemma exists_mem_inter_of_large_density {X : Type*} [Fintype X]
    (S T : Finset X) (η θ : ℝ)
    (hS : 1 - η ≤ (S.dens : ℝ)) (hT : θ / 2 ≤ (T.dens : ℝ))
    (hηθ : η < θ / 2) : ∃ x, x ∈ S ∧ x ∈ T := by
  classical
  by_contra h
  have h_inter_empty : S ∩ T = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun x hx => h ⟨x, Finset.mem_inter.1 hx⟩
  have h_union_dens : ((S ∪ T).dens : ℝ) = (S.dens : ℝ) + (T.dens : ℝ) := by
    have h_disjoint : Disjoint S T :=
      Finset.disjoint_iff_inter_eq_empty.mpr h_inter_empty
    exact_mod_cast Finset.dens_union_of_disjoint h_disjoint
  have h_dens_le_one : ((S ∪ T).dens : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one (s := S ∪ T)
  linarith

/-- The correlated-fiber threshold is at most one in the admissible parameter range. -/
lemma Parameters.θ_le_one {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₁ : δ ≤ 1) :
    Parameters.θ k δ ≤ 1 := by
  unfold θ
  have hden_pos : 0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ :=
    θ_denominator_pos hk δ
  have hm₀_pos : 0 < m₀ k δ := m₀_pos k δ
  have h_one_le_diff : 1 ≤ ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
    have h1 : ((k + 1 : ℕ) : ℝ) ^ 1 - (k : ℝ) ^ 1 = (1 : ℝ) := by norm_num
    simpa [h1] using power_difference_mono k (Nat.succ_le_of_lt hm₀_pos)
  refine (div_le_one hden_pos).mpr ?_
  linarith

/-- Correlated fibers yield either a dense fixed suffix or a fixed suffix supporting many
complete parameter lines. -/
lemma exists_suffix_many_lines {k m : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (Fin m → Fin (k + 1))]
    [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (hfiber : ∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, concat (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    (∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤
      ((suffixPullback V A y).dens : ℝ)) ∨
    ∃ y, δ - 2 * Parameters.η k δ ≤ ((suffixPullback V A y).dens : ℝ) ∧
      Parameters.θ k δ / 2 ≤ ((suffixLines V A y).dens : ℝ) := by
  classical
  let f := fun y : κ → Fin (k + 1) ↦ ((suffixPullback V A y).dens : ℝ)
  let g := fun y : κ → Fin (k + 1) ↦ ((suffixLines V A y).dens : ℝ)
  by_cases hinc : ∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤ f y
  · exact Or.inl hinc
  refine Or.inr ?_
  have hη₀ : 0 < Parameters.η k δ := Parameters.η_pos hk hδ₀
  have hη₁ : Parameters.η k δ ≤ 1 :=
    (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  have havgf : δ - Parameters.η k δ ^ 2 / 2 ≤ 𝔼 y, f y := by
    exact average_suffixPullback_lower V A _ hfiber
  have hupper : ∀ y, f y < δ + Parameters.η k δ ^ 2 / 2 := by
    intro y
    exact lt_of_not_ge fun hy ↦ hinc ⟨y, hy⟩
  have hmostly : 1 - Parameters.η k δ ≤
      ((Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y).dens : ℝ) := by
    refine density_near_average f δ (Parameters.η k δ) hη₀ hη₁ ?_ ?_ havgf hupper
    · intro y
      dsimp only [f]
      positivity
    · intro y
      dsimp only [f]
      exact_mod_cast Finset.dens_le_one (s := suffixPullback V A y)
  have havgg : Parameters.θ k δ ≤ 𝔼 y, g y := by
    exact average_suffixLines_lower V A (Parameters.θ k δ) hlines
  have hmany : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y).dens : ℝ) := by
    refine density_half_threshold g (Parameters.θ k δ) (Parameters.θ_pos hk hδ₀)
      (Parameters.θ_le_one hk hδ₁) ?_ ?_ havgg
    · intro y
      dsimp only [g]
      positivity
    · intro y
      dsimp only [g]
      exact_mod_cast Finset.dens_le_one (s := suffixLines V A y)
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_inter_of_large_density
    (Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y)
    (Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y)
    (Parameters.η k δ) (Parameters.θ k δ) hmostly hmany
    (Parameters.η_lt_θ_div_two hk hδ₀)
  refine ⟨y, ?_, ?_⟩
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f] using hy₁
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g] using hy₂

/-- Fixing a suffix and reindexing preserves the relative-density and complete-line statistics.
The proof is coordinate bookkeeping using `Subspace.reindex_apply` and `Finset.mem_map_equiv`. -/
lemma Subspace.fixSuffixReindex_statistics {k m : ℕ} {ι κ ζ : Type*}
    [Fintype (Fin m → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ζ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (e : ι ⊕ κ ≃ ζ) (A : Finset (ζ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (y : κ → Fin (k + 1)) :
    let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
    (Subspace.relativeDensity (Subspace.fixSuffixReindex e V y) A : ℝ) =
        ((suffixPullback V A' y).dens : ℝ) ∧
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, Subspace.fixSuffixReindex e V y (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) =
        ((suffixLines V A' y).dens : ℝ) := by
  intro A'
  have h_fixSuffix_eval (x : Fin m → Fin (k + 1)) :
      (Subspace.fixSuffix V y : (Fin m → Fin (k + 1)) → (ι ⊕ κ → Fin (k + 1))) x
        = DensityHalesJewett.concat (V x) y := by
    ext j
    cases j with
    | inl i =>
      simp [Subspace.fixSuffix, DensityHalesJewett.concat, Combinatorics.Subspace.coe_apply]
    | inr k =>
      simp [Subspace.fixSuffix, DensityHalesJewett.concat, Combinatorics.Subspace.coe_apply]
  have h_eval (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x = DensityHalesJewett.concat (V x) y ∘ e.symm := by
    calc
      Subspace.fixSuffixReindex e V y x
          = (Subspace.fixSuffix V y) x ∘ e.symm := by
        ext i
        simp [Subspace.fixSuffixReindex, Combinatorics.Subspace.reindex_apply]
      _ = DensityHalesJewett.concat (V x) y ∘ e.symm := by rw [h_fixSuffix_eval x]
  have h_mem_map (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x ∈ A ↔ DensityHalesJewett.concat (V x) y ∈ A' := by
    rw [h_eval x]
    dsimp [A']
    simp [Finset.mem_map_equiv, Equiv.arrowCongr]
  constructor
  · dsimp [Subspace.relativeDensity, suffixPullback]
    congr
    ext x
    simp [h_mem_map x]
  · dsimp [suffixLines]
    congr
    ext l
    refine ⟨fun h a => ?_, fun h a => ?_⟩
    · rw [← h_mem_map (Fin.castSucc ∘ l a)]
      exact h a
    · rw [h_mem_map (Fin.castSucc ∘ l a)]
      exact h a

/-- A bound for the many-lines lemma. -/
noncomputable def manyLinesBound (k m : ℕ) (δ : ℝ) : ℕ :=
  correlatedFibersBound k m δ

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
lemma exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * Parameters.η k δ ≤ (Subspace.relativeDensity V A : ℝ) ∧
      Parameters.θ k δ / 2 ≤
        ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  classical
  let p := correlatedFibersBound k m δ
  let q := n - p
  have hpn : p ≤ n := by
    simpa only [manyLinesBound, p] using hn
  have hpq : p + q = n := Nat.add_sub_of_le hpn
  let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
  let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
  have hA' : δ ≤ (A'.dens : ℝ) := by
    simpa only [A', Finset.dens_map_equiv] using hA
  obtain ⟨W, hWfiber, hWlines⟩ :=
    exists_subspace_correlated_fibers hk hDHJ m hm δ hδ₀ hδ₁
      (ι := Fin p) (κ := Fin q) (by
        simp only [Fintype.card_fin]
        exact le_rfl) A' hA'
  obtain ⟨y, hy⟩ | ⟨y, hy, hylines⟩ :=
    exists_suffix_many_lines hk δ hδ₀ hδ₁ A' W hWfiber hWlines
  · refine Or.inl ⟨Subspace.fixSuffixReindex e W y, ?_⟩
    rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
    simpa only [A'] using hy
  · refine Or.inr ⟨Subspace.fixSuffixReindex e W y, ?_, ?_⟩
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
      simpa only [A'] using hy
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).2]
      simpa only [A'] using hylines

/-- A power of the restricted-alphabet proportion eventually falls below the error tolerance. -/
lemma exists_restrictedParameterWords_decay {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    ∃ m : ℕ, ((k : ℝ) / (k + 1)) ^ m < Parameters.η k δ := by
  apply exists_pow_lt_of_lt_one (Parameters.η_pos hk hδ₀)
  apply (div_lt_one (by positivity : 0 < (k + 1 : ℝ))).mpr
  norm_num

/-- A parameter-cube dimension sufficient for the insensitive-intersection construction. -/
noncomputable def insensitiveIntersectionDimension (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 2 ≤ k ∧ 0 < δ then
    Nat.find (exists_restrictedParameterWords_decay h.1 h.2)
  else 0

/-- Above the selected dimension, the restricted-alphabet proportion is at most the error
tolerance. -/
lemma insensitiveIntersectionDimension_spec {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hm : insensitiveIntersectionDimension k δ ≤ m) :
    ((k : ℝ) / (k + 1)) ^ m ≤ Parameters.η k δ := by
  classical
  rw [insensitiveIntersectionDimension, dif_pos ⟨hk, hδ₀⟩] at hm
  refine (pow_le_pow_of_le_one (by positivity) ?_ hm).trans ?_
  · exact (div_le_one (by positivity : 0 < (k + 1 : ℝ))).mpr (by norm_num)
  · exact (Nat.find_spec (exists_restrictedParameterWords_decay hk hδ₀)).le

/-- Replace every occurrence of the final alphabet letter by a fixed restricted-alphabet
letter. -/
def replaceLastLetter {k m : ℕ} (i : Fin k) (x : Fin m → Fin (k + 1)) :
    Fin m → Fin (k + 1) :=
  fun c ↦ if x c = Fin.last k then i.castSucc else x c

/-- The endpoint family associated with one restricted-alphabet letter. -/
def endpointFamily {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (i : Fin k) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter fun x ↦ V (replaceLastLetter i x) ∈ A

/-- Parameter words which avoid the final alphabet letter. -/
def restrictedParameterWords (k m : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter fun x ↦ ∀ c, x c ≠ Fin.last k

/-- The restricted parameter words are exactly the pointwise images of `Fin k`-valued words. -/
lemma restrictedParameterWords_eq_map (k m : ℕ) :
    restrictedParameterWords k m =
      Finset.univ.map (Function.Embedding.piCongrRight fun _ : Fin m ↦
        (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) := by
  classical
  ext x
  simp only [restrictedParameterWords, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · intro hx
    let y : Fin m → Fin k := fun c ↦ (x c).castPred (hx c)
    refine ⟨y, ?_⟩
    funext c
    exact Fin.castSucc_castPred (x c) (hx c)
  · rintro ⟨y, rfl⟩ c
    exact Fin.castSucc_ne_last (y c)

/-- The density of restricted parameter words is the expected power of the alphabet ratio. -/
lemma restrictedParameterWords_density (k m : ℕ) :
    ((restrictedParameterWords k m).dens : ℝ) = ((k : ℝ) / (k + 1)) ^ m := by
  rw [restrictedParameterWords_eq_map, Finset.nnratCast_dens, Finset.card_map,
    Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
    Fintype.card_pi_const, Fintype.card_fin]
  rw [div_pow]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- Each endpoint family is insensitive to interchanging its selected letter with the final
letter. -/
lemma endpointFamily_isInsensitive {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k) :
    IsInsensitive i.castSucc (Fin.last k) (endpointFamily A V i) := by
  intro x y hxy
  have hreplace : replaceLastLetter i x = replaceLastLetter i y := by
    funext c
    by_cases hx : x c = i.castSucc ∨ x c = Fin.last k
    · by_cases hy : y c = i.castSucc ∨ y c = Fin.last k
      · rcases hx with hxi | hxlast
        · rcases hy with hyi | hylast
          · simp [replaceLastLetter, hxi, hyi]
          · simp [replaceLastLetter, hxi, hylast]
        · rcases hy with hyi | hylast
          · simp [replaceLastLetter, hxlast, hyi]
          · simp [replaceLastLetter, hxlast, hylast]
      · have hyi : y c ≠ i.castSucc := fun h ↦ hy (Or.inl h)
        have hylast : y c ≠ Fin.last k := fun h ↦ hy (Or.inr h)
        have hxyc : x c = y c := (hxy (y c) hyi hylast c).mpr rfl
        rcases hx with hxi | hxlast
        · exact (hyi (hxyc.symm.trans hxi)).elim
        · exact (hylast (hxyc.symm.trans hxlast)).elim
    · have hxi : x c ≠ i.castSucc := fun h ↦ hx (Or.inl h)
      have hxlast : x c ≠ Fin.last k := fun h ↦ hx (Or.inr h)
      by_cases hy : y c = i.castSucc ∨ y c = Fin.last k
      · have hxyc : y c = x c := (hxy (x c) hxi hxlast c).mp rfl
        rcases hy with hyi | hylast
        · exact (hxi (hxyc.symm.trans hyi)).elim
        · exact (hxlast (hxyc.symm.trans hylast)).elim
      · have hyi : y c ≠ i.castSucc := fun h ↦ hy (Or.inl h)
        have hylast : y c ≠ Fin.last k := fun h ↦ hy (Or.inr h)
        have hxyc : y c = x c := (hxy (x c) hxi hxlast c).mp rfl
        simpa only [replaceLastLetter, if_neg hxlast, if_neg hylast] using hxyc.symm
  simp only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hreplace]

/-- Complete restricted-alphabet parameter lines inject into the intersection of the endpoint
families, giving the required density lower bound. -/
lemma endpointFamily_intersection_dense {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hrestricted : ((restrictedParameterWords k m).dens : ℝ) ≤ 1 / 2)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    Parameters.θ k δ / 4 ≤
      ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
  classical
  let good := Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
    ∀ a, V (Fin.castSucc ∘ l a) ∈ A
  let endpoint := fun l : Combinatorics.Line (Fin k) (Fin m) ↦
    fun c ↦
      match l.idxFun c with
      | none => Fin.last k
      | some a => a.castSucc
  have hinjective : Function.Injective endpoint := by
    intro l l' hll
    cases l with
    | mk f hf =>
      cases l' with
      | mk g hg =>
        congr
        funext c
        cases hfc : f c with
        | none =>
            cases hgc : g c with
            | none => rfl
            | some a =>
                have hc := congrFun hll c
                simp only [endpoint, hfc, hgc] at hc
                exact (Fin.castSucc_ne_last a hc.symm).elim
        | some a =>
            cases hgc : g c with
            | none =>
                have hc := congrFun hll c
                simp only [endpoint, hfc, hgc] at hc
                exact (Fin.castSucc_ne_last a hc).elim
            | some b =>
                have hc := congrFun hll c
                simp only [endpoint, hfc, hgc] at hc
                exact congrArg some (Fin.castSucc_injective k hc)
  let endpointEmbedding :
      Combinatorics.Line (Fin k) (Fin m) ↪ (Fin m → Fin (k + 1)) :=
    ⟨endpoint, hinjective⟩
  have hsubset :
      good.map endpointEmbedding ⊆ IsInsensitive.intersection (endpointFamily A V) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hx
    apply IsInsensitive.mem_intersection.mpr
    intro i
    simp only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and]
    have hgood :
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    have heval :
        replaceLastLetter i (endpoint l) = Fin.castSucc ∘ l i := by
      funext c
      cases hc : l.idxFun c with
      | none =>
          simp [endpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc]
      | some a =>
          simp [endpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc,
            Fin.castSucc_ne_last]
    change V (replaceLastLetter i (endpoint l)) ∈ A
    rw [heval]
    exact hgood i
  have hmono :
      ((good.map endpointEmbedding).dens : ℝ) ≤
        ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens hsubset
  refine (le_trans ?_ hmono)
  have hgood :
      Parameters.θ k δ / 2 ≤ (good.dens : ℝ) := by
    simpa only [good] using hlines
  have hlinepos :
      0 < (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) := by
    have hgoodpos : 0 < (good.dens : ℝ) :=
      (div_pos (Parameters.θ_pos hk hδ₀) (by norm_num)).trans_le hgood
    have hgne : good.Nonempty := by
      apply Finset.dens_pos.mp
      exact_mod_cast hgoodpos
    letI : Nonempty (Combinatorics.Line (Fin k) (Fin m)) := ⟨hgne.choose⟩
    exact_mod_cast Fintype.card_pos
  rw [Finset.nnratCast_dens, Finset.card_map]
  rw [Finset.nnratCast_dens] at hgood hrestricted
  have hlinecard :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    rw [Subspace.card_line k m (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) m
  have hwordcard :
      (Fintype.card (Fin m → Fin (k + 1)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hrestrictedcard :
      (restrictedParameterWords k m).card = k ^ m := by
    rw [restrictedParameterWords_eq_map, Finset.card_map, Finset.card_univ,
      Fintype.card_pi_const, Fintype.card_fin]
  rw [hlinecard] at hgood hlinepos
  rw [hwordcard] at ⊢
  rw [hrestrictedcard, Nat.cast_pow, hwordcard] at hrestricted
  have hwordpos : 0 < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hhalf :
      ((k + 1 : ℕ) : ℝ) ^ m / 2 ≤
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    apply (div_le_iff₀ hwordpos).mp at hrestricted
    nlinarith
  have hθ := Parameters.θ_pos hk hδ₀
  rw [le_div_iff₀ hlinepos] at hgood
  rw [le_div_iff₀ hwordpos]
  nlinarith

/-- In a line-free ambient family, a word lying both in its pullback and in every endpoint family
cannot use the final alphabet letter. -/
lemma pullback_inter_endpointFamily_subset_restricted {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A) :
    pullback V A ∩ IsInsensitive.intersection (endpointFamily A V) ⊆
      restrictedParameterWords k m := by
  intro x hx
  obtain ⟨hxpull, hxinter⟩ := Finset.mem_inter.mp hx
  simp only [restrictedParameterWords, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c hc
  let p : Combinatorics.Line (Fin (k + 1)) (Fin m) := {
    idxFun := fun i ↦ if x i = Fin.last k then none else some (x i)
    proper := ⟨c, if_pos hc⟩
  }
  have hp_last : p (Fin.last k) = x := by
    funext i
    by_cases hi : x i = Fin.last k <;>
      simp only [p, Combinatorics.Line.coe_apply, hi, ↓reduceIte, Option.getD_none,
        Option.getD_some]
  have hp_cast (i : Fin k) : p i.castSucc = replaceLastLetter i x := by
    funext j
    by_cases hj : x j = Fin.last k <;>
      simp only [p, replaceLastLetter, Combinatorics.Line.coe_apply, hj, ↓reduceIte,
        Option.getD_none, Option.getD_some]
  obtain ⟨a, ha⟩ := hfree (Subspace.composeLine V p)
  apply ha
  rw [Subspace.composeLine_apply]
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
  · rw [hp_cast]
    have hi := IsInsensitive.mem_intersection.mp hxinter i
    simpa only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · rw [hp_last]
    simpa only [pullback, Finset.mem_filter, Finset.mem_univ, true_and] using hxpull

/-- In a sufficiently large parameter cube, words avoiding the final letter have density at most
`η`. -/
lemma restrictedParameterWords_density_le_eta {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m) :
    ((restrictedParameterWords k m).dens : ℝ) ≤ Parameters.η k δ := by
  rw [restrictedParameterWords_density]
  exact insensitiveIntersectionDimension_spec hk hδ₀ hm_large

/-- Many complete restricted-alphabet lines yield a large insensitive intersection whose part
inside a line-free family is small.  This packages the endpoint construction, its injective
line count, the identification of the intersection, and the geometric-decay estimate. -/
lemma exists_endpoint_insensitive_intersection {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
      Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
      ((pullback V A ∩ IsInsensitive.intersection C).dens : ℝ) ≤
        Parameters.η k δ := by
  refine ⟨endpointFamily A V, endpointFamily_isInsensitive A V, ?_, ?_⟩
  · refine endpointFamily_intersection_dense hk hδ₀ A V ?_ hlines
    refine (restrictedParameterWords_density_le_eta hk hδ₀ hm_large).trans ?_
    exact (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  · refine le_trans ?_ <|
      restrictedParameterWords_density_le_eta hk hδ₀ hm_large
    exact_mod_cast Finset.dens_mono <|
      pullback_inter_endpointFamily_subset_restricted A V hfree

/-- The numerical parameters turn the absolute density left outside a large intersection into
the required relative density gain. -/
lemma Parameters.large_intersection_complement_gain {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    (δ + 6 * η k δ) * (1 - θ k δ / 4) ≤ δ - 3 * η k δ := by
  have hη : η k δ ≤ δ * θ k δ / 48 :=
    min_le_left (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))
  have hθ := θ_pos hk hδ₀
  nlinarith [mul_nonneg hδ₀.le hθ.le, η_pos hk hδ₀,
    mul_nonneg (η_pos hk hδ₀).le hθ.le]

/-- Removing an intersection of density at least `θ / 4`, while losing at most `η` of a family
of density `δ - 2η`, gives the two complement estimates used below. -/
lemma density_complement_bounds {X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq X] (A C : Finset X) (δ η θ : ℝ)
    (hδ₀ : 0 ≤ δ) (hη₀ : 0 ≤ η) (hA : δ - 2 * η ≤ (A.dens : ℝ))
    (hC : θ / 4 ≤ (C.dens : ℝ))
    (hAC : ((A ∩ C).dens : ℝ) ≤ η)
    (hgain : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η) :
    (δ + 6 * η) * ((Cᶜ).dens : ℝ) ≤ ((A ∩ Cᶜ).dens : ℝ) ∧
      δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
  have hsplitA : ((A ∩ C).dens : ℝ) + ((A ∩ Cᶜ).dens : ℝ) = (A.dens : ℝ) := by
    norm_cast
    simpa only [sdiff_eq_inter_compl] using Finset.dens_inter_add_dens_sdiff A C
  have houtside : δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
    linarith
  have hsplitC : ((Cᶜ).dens : ℝ) + (C.dens : ℝ) = 1 := by
    norm_cast
    simpa only [← compl_eq_univ_sdiff, Finset.dens_univ] using
      Finset.dens_sdiff_add_dens_eq_dens C.subset_univ
  refine ⟨(mul_le_mul_of_nonneg_left ?_ ?_).trans (hgain.trans houtside), houtside⟩
  · linarith
  · nlinarith

/-- A large intersection of insensitive families with a density gain on its complement. -/
lemma exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A)
    (hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (Subspace.relativeDensity V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
        Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
        (δ + 6 * Parameters.η k δ) *
            ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
        δ - 3 * Parameters.η k δ ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  classical
  letI : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
    Fintype.ofInjective (fun l ↦ l.idxFun) fun _ _ h ↦ Combinatorics.Line.ext h
  obtain ⟨V, hV⟩ | ⟨V, hV, hlines⟩ :=
    exists_subspace_many_lines hk hDHJ m hm δ hδ₀ hδ₁ n hn A hA
  · exact False.elim <| (not_lt_of_ge hV) (hsmall V)
  obtain ⟨C, hC, hCdense, hAC⟩ :=
    exists_endpoint_insensitive_intersection hk δ hδ₀ hδ₁ hm_large A V hfree hlines
  refine ⟨V, C, hC, hCdense, ?_⟩
  apply density_complement_bounds
  · exact hδ₀.le
  · exact (Parameters.η_pos hk hδ₀).le
  · simpa only [Subspace.relativeDensity, pullback] using hV
  · exact hCdense
  · exact hAC
  · exact Parameters.large_intersection_complement_gain hk hδ₀

/-- The part of the complement of an indexed intersection at which membership first fails. -/
def firstFailurePiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Finset X :=
  (C i)ᶜ ∩ Finset.univ.filter fun x ↦ ∀ j, j < i → x ∈ C j

/-- Replace the first failed set by its complement, retain the preceding sets, and make all
subsequent constraints vacuous. -/
def firstFailureFamily {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Fin k → Finset X :=
  fun j ↦ if j < i then C j else if j = i then (C j)ᶜ else Finset.univ

/-- Every member of the first-failure family has the required sensitivity pair. -/
lemma firstFailureFamily_isInsensitive {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    ∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j) := by
  intro j
  dsimp [firstFailureFamily]
  by_cases hij : j < i
  · simp [hij, hC j]
  · by_cases hej : j = i
    · rw [hej]
      simpa using (hC i).compl
    · simp [hij, hej, IsInsensitive]

/-- Intersecting the first-failure family recovers its selected piece. -/
lemma firstFailureFamily_intersection {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) :
    IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i := by
  ext x
  simp only [IsInsensitive.mem_intersection, firstFailureFamily, firstFailurePiece,
    Finset.mem_inter, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    refine ⟨?_, fun j hij ↦ ?_⟩
    · have hxi := hx i
      simp only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] at hxi
      exact hxi
    · simpa only [if_pos hij] using hx j
  · rintro ⟨hnot, hbefore⟩ j
    by_cases hij : j < i
    · simpa only [if_pos hij] using hbefore j hij
    · by_cases hji : j = i
      · subst j
        simpa only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] using hnot
      · simp only [if_neg hij, if_neg hji, Finset.mem_univ]

/-- The first-failure pieces cover the complement of the original intersection. -/
lemma firstFailurePiece_biUnion {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    rw [firstFailurePiece, Finset.mem_inter, Finset.mem_compl] at hi
    rw [Finset.mem_compl]
    intro hinter
    exact hi.1 (IsInsensitive.mem_intersection.mp hinter i)
  · rw [Finset.mem_compl]
    intro hx
    have hfailed : ∃ i, x ∉ C i := by
      by_contra h
      push Not at h
      exact hx <| IsInsensitive.mem_intersection.mpr h
    let I := Finset.univ.filter fun i : Fin k ↦ x ∉ C i
    have hI : I.Nonempty := by
      obtain ⟨i, hi⟩ := hfailed
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i := I.min' hI
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [firstFailurePiece, Finset.mem_inter, Finset.mem_compl]
    refine ⟨(Finset.mem_filter.mp (I.min'_mem hI)).2, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hij
    by_contra hj
    have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    exact (not_lt_of_ge (I.min'_le j hjI)) hij

/-- A first-failure piece is disjoint from every piece at a later index. -/
lemma firstFailurePiece_disjoint_of_lt {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) {i j : Fin k} (hij : i < j) :
    Disjoint (firstFailurePiece C i : Set X) (firstFailurePiece C j : Set X) := by
  dsimp only [Disjoint]
  intro x hxi hxj
  simp only [firstFailurePiece, coe_inter, coe_compl, coe_filter, mem_univ, true_and,
    Set.subset_inter_iff] at *
  simp only [Set.bot_eq_empty, Set.subset_empty_iff]
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  exact (hxi.1 hy) (hxj.2 hy i hij)

/-- Distinct first-failure pieces are pairwise disjoint. -/
lemma firstFailurePiece_pairwiseDisjoint {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    (Set.univ : Set (Fin k)).PairwiseDisjoint fun i ↦ (firstFailurePiece C i : Set X) := by
  intro i _ j _ hij
  obtain hij | hji := lt_or_gt_of_ne hij
  · exact firstFailurePiece_disjoint_of_lt C hij
  · exact (firstFailurePiece_disjoint_of_lt C hji).symm

/-- The first-failure partition converts the densities of its pieces, and of their intersections
with `A`, into sums. -/
lemma firstFailurePiece_density_sums {k : ℕ}
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X) :
    (∑ i, ((firstFailurePiece C i).dens : ℝ)) =
        (((IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
      (∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ)) =
        ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  constructor
  · have h := Finset.dens_biUnion (s := Finset.univ) (t := firstFailurePiece C) <|
      Finset.pairwiseDisjoint_coe.mp <| by
        simpa only [Finset.coe_univ] using firstFailurePiece_pairwiseDisjoint C
    rw [firstFailurePiece_biUnion] at h
    rw [← NNRat.cast_sum]
    exact congrArg (fun q : ℚ≥0 ↦ (q : ℝ)) h.symm
  · have hpairwise :
        (Set.univ : Set (Fin k)).PairwiseDisjoint fun i ↦
          (A ∩ firstFailurePiece C i : Set X) :=
      (firstFailurePiece_pairwiseDisjoint C).mono_on fun _ _ ↦
        Set.inter_subset_right
    have h := Finset.dens_biUnion (s := Finset.univ)
      (t := fun i ↦ A ∩ firstFailurePiece C i) <|
        Finset.pairwiseDisjoint_coe.mp <| by
          simpa only [Finset.coe_univ, Finset.coe_inter] using hpairwise
    rw [← Finset.inter_biUnion, firstFailurePiece_biUnion] at h
    rw [← NNRat.cast_sum]
    exact congrArg (fun q : ℚ≥0 ↦ (q : ℝ)) h.symm

/-- The quantitative hypotheses and the first-failure density sums force one piece to be both
large and relatively dense in `A`. -/
lemma exists_dense_firstFailurePiece_of_density_sums {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (_hC : Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ))
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hsumPieces : (∑ i, ((firstFailurePiece C i).dens : ℝ)) =
      (((IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hsumIntersections : (∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ)) =
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  by_contra h
  push Not at h
  let g := Parameters.γ k δ
  let e := Parameters.η k δ
  let c := (((IsInsensitive.intersection C)ᶜ).dens : ℝ)
  let a := ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)
  letI : Nonempty (Fin k) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hk⟩⟩
  have hg₀ : 0 < g := Parameters.γ_pos hk hδ₀
  have he₀ : 0 < e := Parameters.η_pos hk hδ₀
  have hsum_lt :
      ∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ) <
        ∑ i, ((δ + g) * ((firstFailurePiece C i).dens : ℝ) + g) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    by_cases hi : g ≤ ((firstFailurePiece C i).dens : ℝ)
    · linarith [h i (by simpa only [g] using hi)]
    · have hinter :
          ((A ∩ firstFailurePiece C i).dens : ℝ) ≤
            ((firstFailurePiece C i).dens : ℝ) := by
        exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
      have hcoefficient : 0 ≤ δ + g := by
        linarith
      nlinarith [mul_nonneg hcoefficient
        (by positivity : 0 ≤ ((firstFailurePiece C i).dens : ℝ))]
  have hupper : a < (δ + g) * c + (k : ℝ) * g := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_lt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum_lt
    rw [hsumPieces, hsumIntersections] at hsum_lt
    exact hsum_lt
  have hac : a ≤ c := by
    dsimp only [a, c]
    exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
  have hc : δ / 2 ≤ c := by
    dsimp only [a, c] at hlarge hac
    linarith [Parameters.η_le_δ_div_six k δ]
  have hcoef : 3 * e ≤ 6 * e - g := by
    dsimp only [e, g]
    linarith [Parameters.γ_le_three_mul_η k δ]
  have hleft :
      3 * e * (δ / 2) ≤ (6 * e - g) * c := by
    exact mul_le_mul hcoef hc (by positivity) (by linarith)
  have hk_real : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk)
  have hright : (k : ℝ) * g ≤ δ * e ^ 2 := by
    have hdiv : g ≤ δ * e ^ 2 / (k : ℝ) := by
      dsimp only [g, e]
      unfold Parameters.γ
      exact min_le_left _ _
    simpa only [mul_comm] using (le_div_iff₀ hk_real).mp hdiv
  have hstrict : δ * e ^ 2 < 3 * e * (δ / 2) := by
    dsimp only [e]
    nlinarith [Parameters.η_le_δ_div_six k δ]
  have hgap : (6 * e - g) * c < (k : ℝ) * g := by
    dsimp only [a, c, e, g] at hweighted hupper
    nlinarith
  exact (not_lt_of_ge hleft) (hgap.trans_le hright |>.trans hstrict)

/-- The first-failure partition and its quantitative weighted averaging.

The complement of `intersection C` is partitioned by `firstFailurePiece C i`.  The two global
density estimates ensure that one piece is both large enough and has the required relative
`A`-density. -/
lemma exists_dense_firstFailurePiece {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (hC : Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ))
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  obtain ⟨hsumPieces, hsumIntersections⟩ :=
    firstFailurePiece_density_sums A C
  exact exists_dense_firstFailurePiece_of_density_sums hk hδ₀ hδ₁ A C hC hweighted
    hlarge hsumPieces hsumIntersections

/-- The Boolean reconstruction of a first-failure piece as an insensitive intersection.

Complement closure preserves the sensitivity pair at the failure index, while the universal
sets after that index impose no constraints. -/
lemma firstFailureFamily_facts {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    (∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j)) ∧
      IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i ∧
      Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint fun j ↦
        (firstFailurePiece C j : Set (ι → Fin (k + 1))) := by
  exact ⟨firstFailureFamily_isInsensitive C hC i,
    firstFailureFamily_intersection C i, firstFailurePiece_biUnion C,
    firstFailurePiece_pairwiseDisjoint C⟩

/-- Correlation with a positive-density intersection of insensitive families. -/
lemma exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (D i)) ∧
        Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ) ∧
        (δ + Parameters.γ k δ) * ((IsInsensitive.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ) := by
  classical
  by_cases hlarge : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)
  · obtain ⟨V, hV⟩ := hlarge
    letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    letI : DecidableEq (Fin m → Fin (k + 1)) := Classical.decEq _
    let D := fun _ : Fin k ↦ (Finset.univ : Finset (Fin m → Fin (k + 1)))
    have hD : IsInsensitive.intersection D = Finset.univ := by
      simpa only [IsInsensitive.intersection, D] using
        (Finset.inf_const (s := (Finset.univ : Finset (Fin k))) Finset.univ_nonempty
          (Finset.univ : Finset (Fin m → Fin (k + 1))))
    refine ⟨V, D, ?_, ?_, ?_⟩
    · intro i x y _
      simp only [D, Finset.mem_univ]
    · rw [hD]
      norm_num
      nlinarith [Parameters.η_le_δ_div_six k δ,
        Parameters.γ_le_η_sq_div_two k δ, Parameters.η_pos hk hδ₀,
        sq_nonneg (1 - Parameters.η k δ)]
    · rw [hD]
      norm_num
      change δ + Parameters.γ k δ ≤ (Subspace.relativeDensity V A : ℝ)
      linarith [Parameters.γ_le_η_sq_div_two k δ]
  · have hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        (Subspace.relativeDensity V A : ℝ) <
          δ + Parameters.η k δ ^ 2 / 2 := by
      intro V
      exact lt_of_not_ge fun hV ↦ hlarge ⟨V, hV⟩
    obtain ⟨V, C, hC, hCdense, hweighted, houtside⟩ :=
      exists_large_insensitive_intersection hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hn A hA
        hfree hsmall
    obtain ⟨i, hidense, hicorrelation⟩ :=
      exists_dense_firstFailurePiece hk hδ₀ hδ₁ (pullback V A) C hCdense hweighted
        houtside
    obtain ⟨hD, hintersection, _, _⟩ := firstFailureFamily_facts C hC i
    refine ⟨V, firstFailureFamily C i, hD, ?_, ?_⟩
    · rw [hintersection]
      exact hidense
    · rw [hintersection]
      exact hicorrelation

/-- An ambient dimension supports all working dimensions needed by the density-increment
dichotomy. -/
def IncrementBoundSufficient (k d : ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 2 ≤ k), HasDensityHJ k → 1 ≤ d → 0 < δ → δ ≤ 1 →
    ∃ m, 1 ≤ m ∧
      insensitiveIntersectionDimension k δ ≤ m ∧
      manyLinesBound k m δ ≤ n ∧
      IsInsensitive.intersectionTilingBound k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m

/-- Sufficient ambient dimensions for the density-increment dichotomy occur eventually. -/
lemma exists_eventually_incrementBoundSufficient (k d : ℕ) (δ : ℝ) :
    ∃ N, ∀ n ≥ N, IncrementBoundSufficient k d δ n := by
  let m := max (max 1 (insensitiveIntersectionDimension k δ))
    (IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))))
  refine ⟨manyLinesBound k m δ, ?_⟩
  intro n hn _ _ _ _ _
  refine ⟨m, ?_, ?_, hn, ?_⟩ <;>
    dsimp only [m] <;> omega

/-- A sufficient ambient dimension for the density-increment dichotomy. -/
noncomputable def incrementBound (k d : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_eventually_incrementBoundSufficient k d δ)

/-- Select one working dimension supporting both structured correlation and the final tiling
argument.

The bound simultaneously leaves enough ambient coordinates for the many-lines construction and
makes the resulting parameter cube large enough for the insensitive-intersection construction and
for tiling that intersection by `d`-subspaces. -/
lemma incrementBound_spec {k d : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {n : ℕ} (hn : incrementBound k d δ ≤ n) :
    ∃ m, 1 ≤ m ∧
      insensitiveIntersectionDimension k δ ≤ m ∧
      manyLinesBound k m δ ≤ n ∧
      IsInsensitive.intersectionTilingBound k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m := by
  classical
  unfold incrementBound at hn
  exact Nat.find_spec (exists_eventually_incrementBoundSufficient k d δ) n hn
    hk hDHJ hd hδ₀ hδ₁

/-- The insensitive-intersection tiling theorem supplies a nonempty finite family of disjoint
`d`-subspaces with small uncovered part. -/
lemma exists_finite_structured_tiling {k d m : ℕ}
    (hk : 2 ≤ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_tiling : IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ)) :
    ∃ 𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)),
      𝒱.Nonempty ∧
      (∀ W ∈ 𝒱, Subspace.IsContained W (IsInsensitive.intersection D)) ∧
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint fun W ↦
        (Subspace.range W : Set (Fin m → Fin (k + 1)))) ∧
      ((IsInsensitive.uncovered (η := Fin d)
        (IsInsensitive.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2 := by
  classical
  let β := Parameters.γ k δ ^ 2 / (4 * (k : ℝ))
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hγ₁ : Parameters.γ k δ ≤ 1 := by
    linarith [Parameters.γ_le_three_mul_η k δ,
      Parameters.η_le_δ_div_six k δ]
  have hβ₀ : 0 < β := by
    dsimp only [β]
    positivity
  have hβ₁ : β ≤ 1 := by
    have hk_real : (2 : ℝ) ≤ k := by
      exact_mod_cast hk
    apply (div_le_iff₀ (by positivity : 0 < 4 * (k : ℝ))).mpr
    nlinarith [sq_nonneg (1 - Parameters.γ k δ)]
  have hβ_simplify :
      2 * (k : ℝ) * β = Parameters.γ k δ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  have hDβ :
      2 * (k : ℝ) * β ≤ ((IsInsensitive.intersection D).dens : ℝ) := by
    rw [hβ_simplify]
    nlinarith
  obtain ⟨𝒱, h𝒱finite, hcontained, hpairwise, huncovered⟩ :=
    IsInsensitive.exists_disjoint_subspaces_iInter (k := k) k d m (by omega) le_rfl hd
      β hβ₀ hβ₁ hm_tiling D (by
        simpa only [Fin.castLE_rfl, id_eq] using hD) hDβ
  have h𝒱nonempty : 𝒱.Nonempty := by
    by_contra h𝒱
    rw [Set.not_nonempty_iff_eq_empty.mp h𝒱] at huncovered
    have hempty :
        IsInsensitive.uncovered (η := Fin d)
          (IsInsensitive.intersection D) (∅ : Set _) =
            IsInsensitive.intersection D := by
      ext x
      simp [IsInsensitive.uncovered]
    rw [hempty, hβ_simplify] at huncovered
    nlinarith
  refine ⟨h𝒱finite.toFinset, h𝒱finite.toFinset_nonempty.mpr h𝒱nonempty, ?_, ?_, ?_⟩
  · intro W hW
    exact hcontained W (h𝒱finite.mem_toFinset.mp hW)
  · simpa only [h𝒱finite.coe_toFinset] using hpairwise
  · simpa only [h𝒱finite.coe_toFinset, hβ_simplify] using huncovered

/-- The structured correlation and the small uncovered part give an aggregate density gain over
the disjoint tile family. -/
lemma structured_tiling_density_sum {k d m n : ℕ}
    (hk : 2 ≤ k) {δ : ℝ} (hδ₀ : 0 < δ) (_hδ₁ : δ ≤ 1)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (hcontained : ∀ W ∈ 𝒱, Subspace.IsContained W (IsInsensitive.intersection D))
    (hpairwise :
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint fun W ↦
      (Subspace.range W : Set (Fin m → Fin (k + 1)))))
    (huncovered :
      ((IsInsensitive.uncovered (η := Fin d)
        (IsInsensitive.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2) :
    (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ) := by
  classical
  let C := IsInsensitive.intersection D
  let P := pullback V A
  let T := 𝒱.biUnion Subspace.range
  have hTsub : T ⊆ C := by
    intro x hx
    simp only [T, Finset.mem_biUnion] at hx
    obtain ⟨W, hW, hxW⟩ := hx
    obtain ⟨z, rfl⟩ := Subspace.mem_range.mp hxW
    exact hcontained W hW z
  have hpairwise_fin :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        Subspace.range := by
    intro W hW W' hW' hne
    apply Finset.disjoint_left.mpr
    intro x hxW hxW'
    exact Set.disjoint_left.mp (hpairwise hW hW' hne) hxW hxW'
  have hsumT :
      ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) = (T.dens : ℝ) := by
    exact_mod_cast (Finset.dens_biUnion hpairwise_fin).symm
  have hpairwise_inter :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        (fun W ↦ P ∩ Subspace.range W) := by
    intro W hW W' hW' hne
    exact (hpairwise_fin hW hW' hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hinterT :
      𝒱.biUnion (fun W ↦ P ∩ Subspace.range W) = P ∩ T := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, T]
    aesop
  have hsumPT :
      ∑ W ∈ 𝒱, ((P ∩ Subspace.range W).dens : ℝ) = ((P ∩ T).dens : ℝ) := by
    rw [← hinterT]
    exact_mod_cast (Finset.dens_biUnion hpairwise_inter).symm
  have huncovered_eq : IsInsensitive.uncovered (η := Fin d) C (𝒱 : Set _) = C \ T := by
    ext x
    simp [IsInsensitive.uncovered, T]
  have hPT_eq : (P ∩ C) ∩ T = P ∩ T := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hxP, _⟩, hxT⟩
      exact ⟨hxP, hxT⟩
    · rintro ⟨hxP, hxT⟩
      exact ⟨⟨hxP, hTsub hxT⟩, hxT⟩
  have hremainder :
      ((P ∩ C) \ T).dens ≤ (C \ T).dens := by
    apply Finset.dens_le_dens
    intro x hx
    obtain ⟨hxPC, hxT⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hxPC).2, hxT⟩
  have hremainder_real :
      (((P ∩ C) \ T).dens : ℝ) ≤ ((C \ T).dens : ℝ) := by
    exact_mod_cast hremainder
  have hdecomp :
      ((P ∩ T).dens : ℝ) + (((P ∩ C) \ T).dens : ℝ) =
        ((P ∩ C).dens : ℝ) := by
    norm_cast
    simpa only [hPT_eq] using Finset.dens_inter_add_dens_sdiff (P ∩ C) T
  have hTdens : (T.dens : ℝ) ≤ (C.dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens hTsub
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hcoefficient : 0 ≤ δ + Parameters.γ k δ / 2 := by
    linarith
  rw [hsumT, hsumPT]
  refine (mul_le_mul_of_nonneg_left hTdens hcoefficient).trans ?_
  rw [huncovered_eq] at huncovered
  dsimp only [C, P] at hDdense hcorrelation huncovered hdecomp hremainder_real hTdens ⊢
  nlinarith

/-- Intersecting a family with a subspace range factors its ambient density into relative density
and range density. -/
lemma Subspace.dens_inter_range_eq_relativeDensity_mul_range
    {η α ι : Type*} [Fintype (η → α)] [Fintype (ι → α)]
    [DecidableEq (ι → α)]
    (W : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    ((A ∩ range W).dens : ℝ) =
      (relativeDensity W A : ℝ) * ((range W).dens : ℝ) := by
  classical
  let B := Finset.univ.filter fun x : η → α ↦ W x ∈ A
  have hAB : A ∩ range W = B.image W := by
    ext w
    simp only [B, range, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, x, hx⟩
      exact ⟨x, hx.symm ▸ hw, hx⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨hxy ▸ hx, x, hxy⟩
  rw [hAB]
  simp only [Finset.nnratCast_dens, relativeDensity, range, B]
  rw [Finset.card_image_iff.mpr (Subspace.injective W).injOn,
    Finset.card_image_iff.mpr (Subspace.injective W).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · letI : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hB : (Finset.univ.filter fun x : η → α ↦ W x ∈ A) = ∅ :=
      Subsingleton.elim _ _
    rw [hB]
    simp
  · field_simp
    simp only [Finset.card_univ]

/-- Finite weighted averaging selects a tile whose pullback density realizes the aggregate
gain. -/
lemma exists_dense_tile_of_density_sum {k d m n : ℕ} (_hk : 2 ≤ k)
    {δ : ℝ} (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (h𝒱 : 𝒱.Nonempty)
    (hsum : (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) :
    ∃ W ∈ 𝒱,
      δ + Parameters.γ k δ / 2 ≤
        (Subspace.relativeDensity W (pullback V A) : ℝ) := by
  by_contra h
  push Not at h
  apply (not_lt_of_ge hsum)
  calc
    (∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) <
        ∑ W ∈ 𝒱, (δ + Parameters.γ k δ / 2) *
          ((Subspace.range W).dens : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty h𝒱
      intro W hW
      rw [Subspace.dens_inter_range_eq_relativeDensity_mul_range]
      apply mul_lt_mul_of_pos_right (h W hW)
      exact_mod_cast Finset.dens_pos.mpr
        ⟨W (fun _ ↦ 0), Subspace.mem_range.mpr ⟨fun _ ↦ 0, rfl⟩⟩
    _ = (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) := by
      rw [Finset.mul_sum]

/-- Relative density in a composite subspace is relative density in the inner subspace of the
outer pullback. -/
lemma Subspace.relativeDensity_compose {α η ζ ι : Type*}
    [Fintype (η → α)] [Fintype (ζ → α)] [DecidableEq (η → α)]
    [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    (relativeDensity (compose V W) A : ℝ) =
      (relativeDensity W (pullback V A) : ℝ) := by
  simp only [relativeDensity, pullback, Finset.mem_filter, Finset.mem_univ, true_and,
    compose_apply]

/-- Tile a structured insensitive intersection and extract a dense tile.

Apply `IsInsensitive.exists_disjoint_subspaces_iInter` with error
`γ² / (4k)`.  Pairwise disjointness turns the densities on the tile ranges into finite sums, and
the uncovered-density estimate preserves half of the correlation gain.  Finite averaging then
selects one `d`-tile of relative `A`-density at least `δ + γ/2`; composing that tile with `V`
gives the required ambient subspace. -/
lemma exists_density_increment_subspace_of_structured_correlation {k d m n : ℕ}
    (hk : 2 ≤ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_tiling : IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
      δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity W A : ℝ) := by
  obtain ⟨𝒱, h𝒱, hcontained, hpairwise, huncovered⟩ :=
    exists_finite_structured_tiling hk hd hδ₀ hδ₁ hm_tiling D hD hDdense
  obtain ⟨W, _, hW⟩ :=
    exists_dense_tile_of_density_sum hk A V 𝒱 h𝒱 <|
      structured_tiling_density_sum hk hδ₀ hδ₁ A V D hDdense hcorrelation 𝒱
        hcontained hpairwise huncovered
  refine ⟨Subspace.compose V W, ?_⟩
  rw [Subspace.relativeDensity_compose]
  exact hW

/-- A dense word family either contains a line or has increased density on a prescribed-dimensional
subspace. -/
lemma density_increment {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : incrementBound k d δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  classical
  by_cases hfree : IsLineFree A
  · obtain ⟨m, hm, hm_large, hmn, hm_tiling⟩ :=
      incrementBound_spec hk hDHJ hd hδ₀ hδ₁ hn
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (Combinatorics.Line (Fin k) (Fin m)) :=
      ⟨Combinatorics.Line.diagonal (Fin k) (Fin m)⟩
    obtain ⟨V, D, hD, hDdense, hcorrelation⟩ :=
      exists_structured_correlation hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hmn A hA hfree
    exact Or.inr <|
      exists_density_increment_subspace_of_structured_correlation hk hd hδ₀ hδ₁ hm_tiling
        A V D hD hDdense hcorrelation
  · rw [IsLineFree] at hfree
    push Not at hfree
    exact Or.inl hfree

end DensityHalesJewett

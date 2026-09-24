import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2805

noncomputable section

open Filter
open scoped Interval Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * x / (1 + (n : ℝ) ^ 2 * x ^ 4)

def badPoint (n : ℕ) : ℝ :=
  1 / (n : ℝ)

def epsilon0 : ℝ := 1 / 4

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

def integralSeq (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, term n x

def antiderivativeBoundary (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.arctan ((n : ℝ) * 1 ^ 2) -
    (1 / 2 : ℝ) * Real.arctan ((n : ℝ) * 0 ^ 2)

def witnessValue (n : ℕ) : ℝ :=
  ((n : ℝ) * (1 / (n : ℝ))) /
    (1 + (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 4))

theorem gap1 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) =
      ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
  rfl

theorem gap2 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  simp

theorem gap3 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  exact gap2

theorem gap4 :
    integralSeq = antiderivativeBoundary := by
  funext n
  unfold integralSeq antiderivativeBoundary
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (1 / 2 : ℝ) * Real.arctan ((n : ℝ) * x ^ 2))
    (f' := term n) ?_ ?_
  · intro x hx
    unfold term
    have hden₁ : 1 + ((n : ℝ) * x ^ 2) ^ 2 ≠ 0 := by
      positivity
    have hden₂ : 1 + (n : ℝ) ^ 2 * x ^ 4 ≠ 0 := by
      positivity
    convert
      ((Real.hasDerivAt_arctan ((n : ℝ) * x ^ 2)).comp x
        (((hasDerivAt_id x).pow 2).const_mul (n : ℝ))).const_mul (1 / 2 : ℝ) using 1
    simp only [id_eq]
    field_simp [hden₁, hden₂] <;> ring
  · have hcont : Continuous (term n) := by
      unfold term
      apply Continuous.div
      · exact continuous_const.mul continuous_id
      · exact continuous_const.add
          (continuous_const.mul (continuous_id.pow 4))
      · intro x
        positivity
    exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1

theorem gap5 :
    Tendsto antiderivativeBoundary atTop (𝓝 (Real.pi / 4)) := by
  have harctan :
      Tendsto (fun n : ℕ => Real.arctan (n : ℝ)) atTop
        (𝓝 (Real.pi / 2)) := by
    simpa only [Function.comp_apply] using
      ((Real.tendsto_arctan_atTop.mono_right inf_le_left).comp
        tendsto_natCast_atTop_atTop)
  have hmul :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) * Real.arctan (n : ℝ)) atTop
        (𝓝 ((1 / 2 : ℝ) * (Real.pi / 2))) :=
    tendsto_const_nhds.mul harctan
  have hval : (1 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 := by
    ring
  rw [hval] at hmul
  have hboundary :
      antiderivativeBoundary =
        fun n : ℕ => (1 / 2 : ℝ) * Real.arctan (n : ℝ) := by
    funext n
    simp [antiderivativeBoundary]
  rw [hboundary]
  exact hmul

theorem gap6 :
    Tendsto integralSeq atTop (𝓝 (Real.pi / 4)) := by
  rw [gap4]
  exact gap5

theorem gap7 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) ≠ Real.pi / 4 := by
  rw [gap2]
  exact ne_of_lt (div_pos Real.pi_pos (by norm_num))

theorem gap8 :
    0 < epsilon0 := by
  norm_num [epsilon0]

theorem gap9 :
    epsilon0 < 1 / 2 := by
  norm_num [epsilon0]

theorem gap10 :
    (0 : ℝ) < 1 / 2 := by
  norm_num

theorem gap11 :
    ∀ n : ℕ, 0 < n →
      |term n (badPoint n)| = witnessValue n := by
  intro n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold term badPoint witnessValue
  have hpos :
      0 < (n : ℝ) * (1 / (n : ℝ)) /
        (1 + (n : ℝ) ^ 2 * (1 / (n : ℝ)) ^ 4) := by
    positivity
  rw [abs_of_pos hpos]
  field_simp [hn0]

theorem gap12 :
    ∀ n : ℕ, 2 ≤ n → witnessValue n > 1 / (1 + 1) := by
  intro n hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by
    positivity
  have hn_sq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  have hw :
      witnessValue n = (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1) := by
    unfold witnessValue
    field_simp [hn0] <;> ring
  rw [hw]
  have hden : 0 < (n : ℝ) ^ 2 + 1 := by
    positivity
  apply (lt_div_iff₀ hden).2
  norm_num
  nlinarith

theorem gap13 :
    (1 / (1 + 1) : ℝ) = 1 / 2 := by
  norm_num

theorem gap14 :
    (1 / 2 : ℝ) > epsilon0 := by
  norm_num [epsilon0]

theorem gap15 :
    ∀ n : ℕ, 2 ≤ n → |term n (badPoint n)| > epsilon0 := by
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [gap11 n hnpos]
  have hw := gap12 n hn
  rw [gap13] at hw
  exact lt_trans gap14 hw

theorem gap16 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro h
  unfold UniformlyConvergesOn at h
  obtain ⟨N, hN⟩ := h epsilon0 gap8
  let n : ℕ := max 2 (Nat.succ N)
  have hn2 : 2 ≤ n := by
    exact Nat.le_max_left _ _
  have hNn : N < n := by
    exact lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_max_right _ _)
  have hnpos : 0 < n :=
    lt_of_lt_of_le (by norm_num) hn2
  have hn1 : 1 ≤ n :=
    le_trans (by norm_num) hn2
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn1
  have hmem : badPoint n ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · unfold badPoint
      exact le_of_lt (one_div_pos.mpr hnR)
    · unfold badPoint
      apply (div_le_iff₀ hnR).2
      simpa using hn1R
  have hsmall := hN n hNn (badPoint n) hmem
  simp only [sub_zero] at hsmall
  have hlarge := gap15 n hn2
  exact (not_lt_of_ge (le_of_lt hlarge)) hsmall

end

end ProofGap.Exercise2805

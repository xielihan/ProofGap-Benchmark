import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity

open scoped Interval

namespace ProofGap.Exercise2314

noncomputable section

def oscillatorySign (x : ℝ) : ℝ :=
  Real.sign (Real.sin (Real.log x))

def targetIntegral : ℝ :=
  ∫ x in 0..1, oscillatorySign x

def tailDecomposition : ℝ :=
  -(1 - Real.exp (-Real.pi)) +
    ∑' k : ℕ,
      (-1 : ℝ) ^ k *
        (Real.exp (-(k + 1 : ℕ) * Real.pi) -
          Real.exp (-(k + 2 : ℕ) * Real.pi))

def geometricSeries : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * Real.exp (-(k : ℕ) * Real.pi)

def geometricForm : ℝ :=
  -1 + 2 * Real.exp (-Real.pi) * geometricSeries

private lemma exp_neg_nat_mul_pi (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.pi) = Real.exp (-Real.pi) ^ n := by
  rw [show -(n : ℝ) * Real.pi = (n : ℝ) * (-Real.pi) by ring]
  exact Real.exp_nat_mul (-Real.pi) n

private lemma geometricSeries_value :
    geometricSeries = 1 / (1 + Real.exp (-Real.pi)) := by
  let q : ℝ := Real.exp (-Real.pi)
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [Real.pi_pos])
  have hnorm : ‖(-q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hq0]
    exact hq1
  have hsum : HasSum (fun k : ℕ => (-q) ^ k) (1 - (-q))⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hterm : ∀ k : ℕ,
      (-1 : ℝ) ^ k * Real.exp (-(k : ℝ) * Real.pi) = (-q) ^ k := by
    intro k
    rw [exp_neg_nat_mul_pi]
    change (-1 : ℝ) ^ k * q ^ k = (-q) ^ k
    rw [show -q = (-1 : ℝ) * q by ring, mul_pow]
  unfold geometricSeries
  calc
    (∑' k : ℕ, (-1 : ℝ) ^ k * Real.exp (-(k : ℝ) * Real.pi)) =
        ∑' k : ℕ, (-q) ^ k := tsum_congr hterm
    _ = (1 - (-q))⁻¹ := hsum.tsum_eq
    _ = 1 / (1 + Real.exp (-Real.pi)) := by
      dsimp [q]
      simp [div_eq_mul_inv]

private lemma tailDecomposition_value :
    tailDecomposition =
      (Real.exp (-Real.pi) - 1) / (Real.exp (-Real.pi) + 1) := by
  let q : ℝ := Real.exp (-Real.pi)
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [Real.pi_pos])
  have hnorm : ‖(-q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hq0]
    exact hq1
  have hsum : HasSum (fun k : ℕ => (-q) ^ k) (1 - (-q))⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hterm : ∀ k : ℕ,
      (-1 : ℝ) ^ k *
          (Real.exp (-(k + 1 : ℕ) * Real.pi) -
            Real.exp (-(k + 2 : ℕ) * Real.pi)) =
        (q - q ^ 2) * (-q) ^ k := by
    intro k
    rw [exp_neg_nat_mul_pi, exp_neg_nat_mul_pi]
    change
      (-1 : ℝ) ^ k * (q ^ (k + 1) - q ^ (k + 2)) =
        (q - q ^ 2) * (-q) ^ k
    have hneg : (-q) ^ k = (-1 : ℝ) ^ k * q ^ k := by
      rw [show -q = (-1 : ℝ) * q by ring, mul_pow]
    simp only [pow_succ, hneg]
    ring
  have htail :
      (∑' k : ℕ,
        (-1 : ℝ) ^ k *
          (Real.exp (-(k + 1 : ℕ) * Real.pi) -
            Real.exp (-(k + 2 : ℕ) * Real.pi))) =
        (q - q ^ 2) * (1 - (-q))⁻¹ := by
    calc
      (∑' k : ℕ,
        (-1 : ℝ) ^ k *
          (Real.exp (-(k + 1 : ℕ) * Real.pi) -
            Real.exp (-(k + 2 : ℕ) * Real.pi))) =
          ∑' k : ℕ, (q - q ^ 2) * (-q) ^ k := tsum_congr hterm
      _ = (q - q ^ 2) * ∑' k : ℕ, (-q) ^ k := by rw [tsum_mul_left]
      _ = (q - q ^ 2) * (1 - (-q))⁻¹ := by rw [hsum.tsum_eq]
  unfold tailDecomposition
  rw [htail]
  change -(1 - q) + (q - q ^ 2) * (1 - (-q))⁻¹ = (q - 1) / (q + 1)
  rw [show 1 - (-q) = q + 1 by ring]
  have hne : q + 1 ≠ 0 := by positivity
  field_simp [hne] <;> ring

private lemma oscillatorySign_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable oscillatorySign MeasureTheory.volume a b := by
  have harg : Measurable (fun x : ℝ => Real.sin (Real.log x)) :=
    Real.continuous_sin.measurable.comp Real.measurable_log
  have hmeas : Measurable oscillatorySign := by
    unfold oscillatorySign Real.sign
    exact Measurable.ite (measurableSet_lt harg measurable_const)
      measurable_const
      (Measurable.ite (measurableSet_lt measurable_const harg)
        measurable_const measurable_const)
  have hone :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
        MeasureTheory.volume a b := intervalIntegrable_const
  rw [intervalIntegrable_iff] at hone ⊢
  refine hone.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [] with x
  unfold oscillatorySign Real.sign
  split_ifs <;> norm_num

private lemma oscillatorySign_scale (x : ℝ) (hx : 0 ≤ x) :
    oscillatorySign (Real.exp (-Real.pi) * x) = -oscillatorySign x := by
  by_cases hx0 : x = 0
  · subst x
    simp [oscillatorySign, Real.sign]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hsin :
      Real.sin (Real.log (Real.exp (-Real.pi) * x)) =
        -Real.sin (Real.log x) := by
    calc
      Real.sin (Real.log (Real.exp (-Real.pi) * x)) =
          Real.sin (Real.log (Real.exp (-Real.pi)) + Real.log x) := by
            rw [Real.log_mul (Real.exp_ne_zero _) hx0]
      _ = Real.sin (-Real.pi + Real.log x) := by rw [Real.log_exp]
      _ = -Real.sin (Real.log x) := by
        rw [Real.sin_add]
        simp
  unfold oscillatorySign
  rw [hsin]
  rcases lt_trichotomy (Real.sin (Real.log x)) 0 with h | h | h
  · have hn : 0 < -Real.sin (Real.log x) := neg_pos.mpr h
    have hnot : ¬ 0 < Real.sin (Real.log x) := by linarith
    simp [Real.sign, h, hn, hnot]
  · simp [Real.sign, h]
  · have hn : -Real.sin (Real.log x) < 0 := neg_lt_zero.mpr h
    have hnot : ¬ Real.sin (Real.log x) < 0 := by linarith
    simp [Real.sign, h, hn, hnot]

private lemma targetIntegral_value :
    targetIntegral =
      (Real.exp (-Real.pi) - 1) / (Real.exp (-Real.pi) + 1) := by
  let q : ℝ := Real.exp (-Real.pi)
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [Real.pi_pos])
  have hscaled :
      (∫ x in 0..q, oscillatorySign x) =
        -q * (∫ x in 0..1, oscillatorySign x) := by
    have hchange := intervalIntegral.integral_comp_mul_right
      (f := oscillatorySign) (a := 0) (b := 1) (c := q) hq0.ne'
    have hcomp :
        (∫ x in 0..1, oscillatorySign (x * q)) =
          -(∫ x in 0..1, oscillatorySign x) := by
      calc
        (∫ x in 0..1, oscillatorySign (x * q)) =
            ∫ x in 0..1, -oscillatorySign x := by
              apply intervalIntegral.integral_congr
              intro x hx
              have hx' : 0 ≤ x := by
                simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx.1
              simpa [mul_comm] using oscillatorySign_scale x hx'
        _ = -(∫ x in 0..1, oscillatorySign x) := by
          rw [intervalIntegral.integral_neg]
    rw [hcomp] at hchange
    have hrel :
        -(∫ x in 0..1, oscillatorySign x) =
          q⁻¹ * (∫ x in 0..q, oscillatorySign x) := by
      simpa using hchange
    calc
      (∫ x in 0..q, oscillatorySign x) =
          q * (q⁻¹ * (∫ x in 0..q, oscillatorySign x)) := by
            field_simp [hq0.ne']
      _ = q * (-(∫ x in 0..1, oscillatorySign x)) := by rw [← hrel]
      _ = -q * (∫ x in 0..1, oscillatorySign x) := by ring
  have hsecond :
      (∫ x in q..1, oscillatorySign x) = -(1 - q) := by
    have hae :
        ∀ᵐ x ∂MeasureTheory.volume,
          x ∈ Set.uIoc q 1 → oscillatorySign x = (-1 : ℝ) := by
      have hxne : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hxne] with x hxne
      intro hx
      rw [Set.uIoc_of_le (le_of_lt hq1)] at hx
      have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxne
      have hxpos : 0 < x := lt_trans hq0 hx.1
      have hlog_lower : -Real.pi < Real.log x := by
        apply Real.exp_lt_exp.mp
        simpa [q, Real.exp_log hxpos] using hx.1
      have hlog_upper : Real.log x < 0 := by
        apply Real.exp_lt_exp.mp
        simpa [Real.exp_log hxpos] using hxlt
      have hsin : Real.sin (Real.log x) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hlog_upper hlog_lower
      unfold oscillatorySign Real.sign
      simp [hsin]
    calc
      (∫ x in q..1, oscillatorySign x) = ∫ _x in q..1, (-1 : ℝ) :=
        intervalIntegral.integral_congr_ae hae
      _ = -(1 - q) := by simp <;> ring
  have hsplit :
      (∫ x in 0..1, oscillatorySign x) =
        (∫ x in 0..q, oscillatorySign x) +
          ∫ x in q..1, oscillatorySign x := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (oscillatorySign_intervalIntegrable 0 q)
      (oscillatorySign_intervalIntegrable q 1)
  unfold targetIntegral
  rw [hscaled, hsecond] at hsplit
  dsimp [q] at hsplit ⊢
  have hne : Real.exp (-Real.pi) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hne).2
  nlinarith [hsplit]

theorem gap1 :
    targetIntegral = tailDecomposition := by
  rw [targetIntegral_value, tailDecomposition_value]

theorem gap2 :
    targetIntegral = geometricForm := by
  rw [targetIntegral_value, geometricForm, geometricSeries_value]
  have hne : Real.exp (-Real.pi) + 1 ≠ 0 := by positivity
  field_simp [hne]
  ring

theorem gap3 :
    geometricForm =
      -1 + 2 * Real.exp (-Real.pi) / (1 + Real.exp (-Real.pi)) := by
  unfold geometricForm
  rw [geometricSeries_value]
  have hne : Real.exp (-Real.pi) + 1 ≠ 0 := by positivity
  field_simp [hne]

theorem gap4 :
    -1 + 2 * Real.exp (-Real.pi) / (1 + Real.exp (-Real.pi)) =
      (Real.exp (-Real.pi) - 1) / (Real.exp (-Real.pi) + 1) := by
  have hne : Real.exp (-Real.pi) + 1 ≠ 0 := by positivity
  field_simp [hne]
  ring

theorem gap5 :
    (Real.exp (-Real.pi) - 1) / (Real.exp (-Real.pi) + 1) =
      -Real.tanh (Real.pi / 2) := by
  have hmul :
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2)) = 1 := by
    calc
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2)) =
          Real.exp (Real.pi / 2 + -(Real.pi / 2)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp 0 := by
        congr 1
        ring
      _ = 1 := Real.exp_zero
  have hsq :
      Real.exp (-Real.pi) =
        Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 2)) := by
    calc
      Real.exp (-Real.pi) =
          Real.exp (-(Real.pi / 2) + -(Real.pi / 2)) := by
        congr 1
        ring
      _ = Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 2)) :=
        Real.exp_add _ _
  have hmulB :
      Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2)) *
          Real.exp (-(Real.pi / 2)) =
        Real.exp (-(Real.pi / 2)) := by
    rw [hmul]
    ring
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hsq]
  have hleft :
      Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 2)) + 1 ≠ 0 := by
    positivity
  have hcosh :
      Real.exp (Real.pi / 2) + Real.exp (-(Real.pi / 2)) ≠ 0 := by
    positivity
  field_simp [hleft, hcosh] <;> nlinarith [hmulB]

theorem gap6 :
    targetIntegral = -Real.tanh (Real.pi / 2) := by
  exact gap2.trans (gap3.trans (gap4.trans gap5))

end

end ProofGap.Exercise2314

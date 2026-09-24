import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2477

noncomputable section

def upper (a b x : ℝ) : ℝ := b + Real.sqrt (a ^ 2 - x ^ 2)

def lower (a b x : ℝ) : ℝ := b - Real.sqrt (a ^ 2 - x ^ 2)

def volume (a b : ℝ) : ℝ :=
  Real.pi * ∫ x in -a..a, (upper a b x ^ 2 - lower a b x ^ 2)

private theorem semicircle_integral_eq_two_quarter (a : ℝ) :
    (∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) =
      2 * (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) := by
  have hf : Continuous (fun x : ℝ => Real.sqrt (a ^ 2 - x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  have hsymm :
      (∫ x in -a..0, Real.sqrt (a ^ 2 - x ^ 2)) =
        ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
    calc
      (∫ x in -a..0, Real.sqrt (a ^ 2 - x ^ 2)) =
          ∫ x in 0..a, Real.sqrt (a ^ 2 - (-x) ^ 2) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg
            (f := fun x : ℝ => Real.sqrt (a ^ 2 - x ^ 2))
            (a := 0) (b := a)).symm
      _ = ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _
        apply congrArg Real.sqrt
        ring
  calc
    (∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) =
        (∫ x in -a..0, Real.sqrt (a ^ 2 - x ^ 2)) +
          ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
            symm
            exact intervalIntegral.integral_add_adjacent_intervals
              (hf.intervalIntegrable (-a) 0) (hf.intervalIntegrable 0 a)
    _ = 2 * (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) := by
      rw [hsymm]
      ring

private theorem quarter_circle_integral (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) =
      Real.pi * a ^ 2 / 4 := by
  have hg : Continuous (fun x : ℝ => Real.sqrt (a ^ 2 - x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  have hφcont : Continuous (fun t : ℝ => a * Real.sin t) :=
    continuous_const.mul Real.continuous_sin
  have hφ'cont : Continuous (fun t : ℝ => a * Real.cos t) :=
    continuous_const.mul Real.continuous_cos
  have hφ (t : ℝ) :
      HasDerivAt (fun s : ℝ => a * Real.sin s) (a * Real.cos t) t := by
    simpa using (Real.hasDerivAt_sin t).const_mul a
  have hprim (y : ℝ) :
      HasDerivAt
        (fun z : ℝ =>
          ∫ x in (0 : ℝ)..z, Real.sqrt (a ^ 2 - x ^ 2))
        (Real.sqrt (a ^ 2 - y ^ 2)) y := by
    apply intervalIntegral.integral_hasDerivAt_right
    all_goals
      first
      | exact hg.continuousAt
      | exact hg.intervalIntegrable _ _
      | exact hg.stronglyMeasurable.stronglyMeasurableAtFilter
  have hcomp (t : ℝ) :
      HasDerivAt
        (fun s : ℝ =>
          ∫ x in (0 : ℝ)..(a * Real.sin s),
            Real.sqrt (a ^ 2 - x ^ 2))
        (Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
          (a * Real.cos t)) t := by
    convert (hprim (a * Real.sin t)).comp t (hφ t) using 1 <;> ring
  have htrans :
      (∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
            (a * Real.cos t)) =
        (∫ x in (0 : ℝ)..(a * Real.sin (Real.pi / 2)),
          Real.sqrt (a ^ 2 - x ^ 2)) -
        ∫ x in (0 : ℝ)..(a * Real.sin 0),
          Real.sqrt (a ^ 2 - x ^ 2) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun s : ℝ =>
        ∫ x in (0 : ℝ)..(a * Real.sin s),
          Real.sqrt (a ^ 2 - x ^ 2))
      (f' := fun t : ℝ =>
        Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
          (a * Real.cos t))
      (fun x _ => hcomp x)
      (((hg.comp hφcont).mul hφ'cont).intervalIntegrable _ _)
  have hchange :
      (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
            (a * Real.cos t) := by
    simpa only [Real.sin_zero, Real.sin_pi_div_two, mul_zero, mul_one,
      intervalIntegral.integral_same, sub_zero] using htrans.symm
  have hcosint :
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 2) =
        Real.pi / 4 := by
    have hF (t : ℝ) :
        HasDerivAt
          (fun s : ℝ => (1 / 2 : ℝ) * s +
            (1 / 4 : ℝ) * Real.sin (2 * s))
          (Real.cos t ^ 2) t := by
      have htwo : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
      have hsin :
          HasDerivAt (fun s : ℝ => Real.sin (2 * s))
            (2 * Real.cos (2 * t)) t := by
        convert (Real.hasDerivAt_sin (2 * t)).comp t htwo using 1 <;> ring
      convert ((hasDerivAt_id t).const_mul (1 / 2 : ℝ)).add
        (hsin.const_mul (1 / 4 : ℝ)) using 1
      rw [Real.cos_two_mul]
      ring
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 2) =
          ((1 / 2 : ℝ) * (Real.pi / 2) +
              (1 / 4 : ℝ) * Real.sin (2 * (Real.pi / 2))) -
            ((1 / 2 : ℝ) * 0 +
              (1 / 4 : ℝ) * Real.sin (2 * 0)) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := Real.pi / 2)
          (f := fun s : ℝ => (1 / 2 : ℝ) * s +
            (1 / 4 : ℝ) * Real.sin (2 * s))
          (f' := fun t : ℝ => Real.cos t ^ 2)
          (fun x _ => hF x)
          ((Real.continuous_cos.pow 2).intervalIntegrable _ _)
      _ = Real.pi / 4 := by
        have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
        rw [hpi, Real.sin_pi]
        simp only [mul_zero, Real.sin_zero, add_zero, sub_zero]
        ring
  calc
    (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
            (a * Real.cos t) := hchange
    _ = ∫ t in (0 : ℝ)..Real.pi / 2,
          a ^ 2 * Real.cos t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hc : (0 : ℝ) ≤ Real.pi / 2 :=
        div_nonneg (le_of_lt Real.pi_pos) (by norm_num)
      have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa only [Set.uIcc_of_le hc] using ht
      have hcos : 0 ≤ Real.cos t := by
        apply Real.cos_nonneg_of_mem_Icc
        exact ⟨le_trans (neg_nonpos.mpr hc) ht'.1, ht'.2⟩
      have htrig :
          1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
        calc
          1 - Real.sin t ^ 2 =
              (Real.sin t ^ 2 + Real.cos t ^ 2) - Real.sin t ^ 2 := by
                rw [Real.sin_sq_add_cos_sq]
          _ = Real.cos t ^ 2 := by ring
      have hsquare :
          a ^ 2 - (a * Real.sin t) ^ 2 =
            (a * Real.cos t) ^ 2 := by
        calc
          a ^ 2 - (a * Real.sin t) ^ 2 =
              a ^ 2 * (1 - Real.sin t ^ 2) := by ring
          _ = a ^ 2 * Real.cos t ^ 2 := by rw [htrig]
          _ = (a * Real.cos t) ^ 2 := by ring
      have hsqrt :
          Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) =
            a * Real.cos t := by
        calc
          Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) =
              Real.sqrt ((a * Real.cos t) ^ 2) := by rw [hsquare]
          _ = |a * Real.cos t| := Real.sqrt_sq_eq_abs _
          _ = a * Real.cos t := abs_of_nonneg (mul_nonneg ha hcos)
      change
        Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
            (a * Real.cos t) =
          a ^ 2 * Real.cos t ^ 2
      rw [hsqrt]
      ring
    _ = a ^ 2 *
        (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * a ^ 2 / 4 := by
      rw [hcosint]
      ring

theorem gap1 (a b x : ℝ) :
    upper a b x = b + Real.sqrt (a ^ 2 - x ^ 2) := by
  rfl

theorem gap2 (a b x : ℝ) :
    lower a b x = b - Real.sqrt (a ^ 2 - x ^ 2) := by
  rfl

theorem gap3 (a x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
    -a ≤ x := by
  exact hx.1

theorem gap4 (a x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
    x ≤ a := by
  exact hx.2

theorem gap5 (a b Vₓ : ℝ) (hV : Vₓ = volume a b) :
    Vₓ = Real.pi * ∫ x in -a..a,
      (upper a b x ^ 2 - lower a b x ^ 2) := by
  simpa [volume] using hV

theorem gap6 (a b Vₓ : ℝ) (ha : 0 ≤ a) (hV : Vₓ = volume a b) :
    Vₓ = 8 * b * Real.pi *
      ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
  calc
    Vₓ = Real.pi * ∫ x in -a..a,
        (upper a b x ^ 2 - lower a b x ^ 2) := gap5 a b Vₓ hV
    _ = Real.pi * ∫ x in -a..a,
        (4 * b) * Real.sqrt (a ^ 2 - x ^ 2) := by
          apply congrArg (fun z : ℝ => Real.pi * z)
          apply intervalIntegral.integral_congr
          intro x _
          simp only [upper, lower]
          ring
    _ = Real.pi * ((4 * b) *
        ∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = 8 * b * Real.pi *
        ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
          rw [semicircle_integral_eq_two_quarter]
          ring

theorem gap7 (a b : ℝ) (ha : 0 ≤ a) :
    8 * b * Real.pi * (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) =
      2 * Real.pi ^ 2 * a ^ 2 * b := by
  rw [quarter_circle_integral a ha]
  ring

theorem gap8 (a b Vₓ : ℝ) (ha : 0 ≤ a) (hV : Vₓ = volume a b) :
    Vₓ = 2 * Real.pi ^ 2 * a ^ 2 * b := by
  calc
    Vₓ = 8 * b * Real.pi *
        ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := gap6 a b Vₓ ha hV
    _ = 2 * Real.pi ^ 2 * a ^ 2 * b := gap7 a b ha

end

end ProofGap.Exercise2477

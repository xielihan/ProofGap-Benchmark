import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2493

noncomputable section

def catenary (a x : ℝ) : ℝ := a * Real.cosh (x / a)

def speed (a x : ℝ) : ℝ :=
  Real.sqrt (1 + deriv (catenary a) x ^ 2)

def xSurface (a b : ℝ) : ℝ :=
  2 * Real.pi * a * ∫ x in -b..b, Real.cosh (x / a) ^ 2

def ySurface (a b : ℝ) : ℝ :=
  2 * Real.pi * ∫ x in 0..b, x * speed a x

private theorem integral_one_add_cosh_formula
    (a b : ℝ) (ha : a ≠ 0) :
    (∫ x in 0..b, (1 + Real.cosh (2 * x / a))) =
      b + a / 2 * Real.sinh (2 * b / a) := by
  have hF (x : ℝ) :
      HasDerivAt
        (fun y : ℝ => y + a / 2 * Real.sinh (2 * y / a))
        (1 + Real.cosh (2 * x / a)) x := by
    have hinner :
        HasDerivAt (fun y : ℝ => 2 * y / a) (2 / a) x := by
      convert (((hasDerivAt_id x).const_mul 2).div_const a) using 1 <;>
        ring
    have hs :=
      (Real.hasDerivAt_sinh (2 * x / a)).comp x hinner
    convert (hasDerivAt_id x).add (hs.const_mul (a / 2)) using 1 <;>
      field_simp [ha] <;> ring
  have harg : Continuous (fun x : ℝ => 2 * x / a) := by
    simpa using (continuous_const.mul continuous_id).div_const a
  have hcont :
      Continuous (fun x : ℝ => 1 + Real.cosh (2 * x / a)) := by
    simpa [Function.comp_def] using
      continuous_const.add (Real.continuous_cosh.comp harg)
  have hint :
      IntervalIntegrable (fun x : ℝ => 1 + Real.cosh (2 * x / a))
        MeasureTheory.volume 0 b :=
    hcont.intervalIntegrable _ _
  have heval :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hF x) hint
  calc
    (∫ x in 0..b, (1 + Real.cosh (2 * x / a))) =
        (fun y : ℝ => y + a / 2 * Real.sinh (2 * y / a)) b -
        (fun y : ℝ => y + a / 2 * Real.sinh (2 * y / a)) 0 := by
      simpa using heval
    _ = b + a / 2 * Real.sinh (2 * b / a) := by simp

theorem gap1 (a x : ℝ) (ha : a ≠ 0) :
    speed a x = Real.sqrt (Real.sinh (x / a) ^ 2 + 1) := by
  have hraw :=
    ((Real.hasDerivAt_cosh (x / a)).comp x
      ((hasDerivAt_id x).div_const a)).const_mul a
  have hd : HasDerivAt (catenary a) (Real.sinh (x / a)) x := by
    unfold catenary
    convert hraw using 1 <;> field_simp [ha] <;> ring
  simp [speed, hd.deriv, add_comm]

theorem gap2 (a x : ℝ) :
    Real.sqrt (Real.sinh (x / a) ^ 2 + 1) = Real.cosh (x / a) := by
  have hidentity := Real.cosh_sq_sub_sinh_sq (x / a)
  have hsquare :
      Real.sinh (x / a) ^ 2 + 1 = Real.cosh (x / a) ^ 2 := by
    nlinarith
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos _)]

theorem gap3 (a x : ℝ) (ha : a ≠ 0) :
    speed a x = Real.cosh (x / a) := by
  rw [gap1 a x ha, gap2 a x]

theorem gap4 (a b Pₓ : ℝ) (hP : Pₓ = xSurface a b) :
    Pₓ = 2 * Real.pi * a *
      ∫ x in -b..b, Real.cosh (x / a) ^ 2 := by
  simpa [xSurface] using hP

theorem gap5 (a b : ℝ) :
    2 * Real.pi * a * (∫ x in -b..b, Real.cosh (x / a) ^ 2) =
      2 * Real.pi * a *
        ∫ x in 0..b, (1 + Real.cosh (2 * x / a)) := by
  by_cases ha : a = 0
  · subst a
    simp
  · have hleft :
        (∫ x in -b..b, Real.cosh (x / a) ^ 2) =
          b + a / 2 * Real.sinh (2 * b / a) := by
      have hF (x : ℝ) :
          HasDerivAt
            (fun y : ℝ => y / 2 + a / 4 * Real.sinh (2 * y / a))
            (Real.cosh (x / a) ^ 2) x := by
        have hinner :
            HasDerivAt (fun y : ℝ => 2 * y / a) (2 / a) x := by
          convert (((hasDerivAt_id x).const_mul 2).div_const a) using 1 <;>
            ring
        have hs :=
          (Real.hasDerivAt_sinh (2 * x / a)).comp x hinner
        have hraw :
            HasDerivAt
              (fun y : ℝ => y / 2 + a / 4 * Real.sinh (2 * y / a))
              (1 / 2 + a / 4 *
                (Real.cosh (2 * x / a) * (2 / a))) x := by
          convert ((hasDerivAt_id x).div_const 2).add
            (hs.const_mul (a / 4)) using 1 <;> ring
        have hdouble := Real.cosh_two_mul (x / a)
        have hhyper := Real.cosh_sq_sub_sinh_sq (x / a)
        convert hraw using 1
        · rw [show 2 * x / a = 2 * (x / a) by ring, hdouble]
          field_simp [ha]
          nlinarith
      have hcont :
          Continuous (fun x : ℝ => Real.cosh (x / a) ^ 2) := by
        simpa [Function.comp_def] using
          (Real.continuous_cosh.comp (continuous_id.div_const a)).pow 2
      have hint :
          IntervalIntegrable (fun x : ℝ => Real.cosh (x / a) ^ 2)
            MeasureTheory.volume (-b) b :=
        hcont.intervalIntegrable _ _
      have heval :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => hF x) hint
      calc
        (∫ x in -b..b, Real.cosh (x / a) ^ 2) =
            (fun y : ℝ =>
              y / 2 + a / 4 * Real.sinh (2 * y / a)) b -
            (fun y : ℝ =>
              y / 2 + a / 4 * Real.sinh (2 * y / a)) (-b) := by
          simpa using heval
        _ = b + a / 2 * Real.sinh (2 * b / a) := by
          simp only
          rw [show 2 * -b / a = -(2 * b / a) by ring,
            Real.sinh_neg]
          ring
    rw [hleft, integral_one_add_cosh_formula a b ha]

theorem gap6 (a b : ℝ) (ha : a ≠ 0) :
    2 * Real.pi * a *
        (∫ x in 0..b, (1 + Real.cosh (2 * x / a))) =
      Real.pi * a * (2 * b + a * Real.sinh (2 * b / a)) := by
  rw [integral_one_add_cosh_formula a b ha]
  ring

theorem gap7 (a b Pₓ : ℝ) (ha : a ≠ 0)
    (hP : Pₓ = xSurface a b) :
    Pₓ = Real.pi * a * (2 * b + a * Real.sinh (2 * b / a)) := by
  calc
    Pₓ = 2 * Real.pi * a *
        (∫ x in -b..b, Real.cosh (x / a) ^ 2) := gap4 a b Pₓ hP
    _ = 2 * Real.pi * a *
        ∫ x in 0..b, (1 + Real.cosh (2 * x / a)) := gap5 a b
    _ = Real.pi * a *
        (2 * b + a * Real.sinh (2 * b / a)) := gap6 a b ha

theorem gap8 (a b Pᵧ : ℝ) (hP : Pᵧ = ySurface a b) :
    Pᵧ = 2 * Real.pi * ∫ x in 0..b, x * speed a x := by
  simpa [ySurface] using hP

theorem gap9 (a b : ℝ) (ha : a ≠ 0) :
    2 * Real.pi * (∫ x in 0..b, x * speed a x) =
      2 * Real.pi * ∫ x in 0..b, x * Real.cosh (x / a) := by
  apply congrArg (fun z : ℝ => 2 * Real.pi * z)
  apply intervalIntegral.integral_congr
  intro x hx
  change x * speed a x = x * Real.cosh (x / a)
  rw [gap3 a x ha]

theorem gap10 (a b : ℝ) (ha : a ≠ 0) :
    2 * Real.pi * (∫ x in 0..b, x * Real.cosh (x / a)) =
      2 * Real.pi * a *
        (a + b * Real.sinh (b / a) - a * Real.cosh (b / a)) := by
  have hF (x : ℝ) :
      HasDerivAt
        (fun y : ℝ =>
          a * y * Real.sinh (y / a) - a ^ 2 * Real.cosh (y / a))
        (x * Real.cosh (x / a)) x := by
    have hs :=
      (Real.hasDerivAt_sinh (x / a)).comp x
        ((hasDerivAt_id x).div_const a)
    have hc :=
      (Real.hasDerivAt_cosh (x / a)).comp x
        ((hasDerivAt_id x).div_const a)
    have hfirst := ((hasDerivAt_id x).const_mul a).mul hs
    have hsecond := hc.const_mul (a ^ 2)
    convert hfirst.sub hsecond using 1
    · simp only [Function.comp_apply, id_eq]
      field_simp [ha]
      ring
  have hcont :
      Continuous (fun x : ℝ => x * Real.cosh (x / a)) := by
    simpa [Function.comp_def] using
      continuous_id.mul
        (Real.continuous_cosh.comp (continuous_id.div_const a))
  have hint :
      IntervalIntegrable (fun x : ℝ => x * Real.cosh (x / a))
        MeasureTheory.volume 0 b :=
    hcont.intervalIntegrable _ _
  have heval :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hF x) hint
  have hi :
      (∫ x in 0..b, x * Real.cosh (x / a)) =
        (fun y : ℝ =>
          a * y * Real.sinh (y / a) - a ^ 2 * Real.cosh (y / a)) b -
        (fun y : ℝ =>
          a * y * Real.sinh (y / a) - a ^ 2 * Real.cosh (y / a)) 0 := by
    simpa using heval
  rw [hi]
  simp
  ring

theorem gap11 (a b Pᵧ : ℝ) (ha : a ≠ 0)
    (hP : Pᵧ = ySurface a b) :
    Pᵧ = 2 * Real.pi * a *
      (a + b * Real.sinh (b / a) - a * Real.cosh (b / a)) := by
  calc
    Pᵧ = 2 * Real.pi *
        (∫ x in 0..b, x * speed a x) := gap8 a b Pᵧ hP
    _ = 2 * Real.pi *
        (∫ x in 0..b, x * Real.cosh (x / a)) := gap9 a b ha
    _ = 2 * Real.pi * a *
        (a + b * Real.sinh (b / a) -
          a * Real.cosh (b / a)) := gap10 a b ha

end

end ProofGap.Exercise2493

import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2448

noncomputable section

def radius (a φ : ℝ) : ℝ := a * (1 + Real.cos φ)

def polarSpeed (a φ : ℝ) : ℝ :=
  Real.sqrt (radius a φ ^ 2 + (-a * Real.sin φ) ^ 2)

def arcLength (a : ℝ) : ℝ :=
  2 * ∫ φ in 0..Real.pi, 2 * a * Real.cos (φ / 2)

theorem gap1 (a φ : ℝ) (ha : 0 ≤ a)
    (hφ₀ : -Real.pi ≤ φ) (hφ₁ : φ ≤ Real.pi) :
    polarSpeed a φ = 2 * a * Real.cos (φ / 2) := by
  unfold polarSpeed radius
  have hhalf : φ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc hhalf
  have hdouble : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (φ / 2) using 1 <;> ring
  have hbase :
      (1 + Real.cos φ) ^ 2 + Real.sin φ ^ 2 =
        4 * Real.cos (φ / 2) ^ 2 := by
    calc
      (1 + Real.cos φ) ^ 2 + Real.sin φ ^ 2 =
          2 * (1 + Real.cos φ) := by
            nlinarith [Real.sin_sq_add_cos_sq φ]
      _ = 4 * Real.cos (φ / 2) ^ 2 := by
            rw [hdouble]
            ring
  have hrad :
      (a * (1 + Real.cos φ)) ^ 2 + (-a * Real.sin φ) ^ 2 =
        (2 * a * Real.cos (φ / 2)) ^ 2 := by
    calc
      (a * (1 + Real.cos φ)) ^ 2 + (-a * Real.sin φ) ^ 2 =
          a ^ 2 * ((1 + Real.cos φ) ^ 2 + Real.sin φ ^ 2) := by ring
      _ = a ^ 2 * (4 * Real.cos (φ / 2) ^ 2) := by rw [hbase]
      _ = (2 * a * Real.cos (φ / 2)) ^ 2 := by ring
  have hrhs : 0 ≤ 2 * a * Real.cos (φ / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) ha) hcos
  rw [hrad, Real.sqrt_sq hrhs]

theorem gap2 (a s : ℝ) (hs : s = arcLength a) :
    s = 2 * ∫ φ in 0..Real.pi, 2 * a * Real.cos (φ / 2) := by
  simpa [arcLength] using hs

theorem gap3 (a : ℝ) :
    2 * (∫ φ in 0..Real.pi, 2 * a * Real.cos (φ / 2)) = 8 * a := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => 4 * a * Real.sin (y / 2))
        (2 * a * Real.cos (x / 2)) x := by
    intro x
    convert
      ((Real.hasDerivAt_sin (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)).const_mul (4 * a) using 1 <;> ring
  have hcont : Continuous (fun x : ℝ => 2 * a * Real.cos (x / 2)) := by
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_id.div_const 2))
  have hinterval :
      IntervalIntegrable (fun x : ℝ => 2 * a * Real.cos (x / 2))
        MeasureTheory.volume 0 Real.pi :=
    hcont.intervalIntegrable 0 Real.pi
  have hInt :
      (∫ φ in (0 : ℝ)..Real.pi, 2 * a * Real.cos (φ / 2)) =
        4 * a * Real.sin (Real.pi / 2) -
          4 * a * Real.sin ((0 : ℝ) / 2) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hinterval
  rw [hInt]
  simp only [Real.sin_pi_div_two, zero_div, Real.sin_zero, mul_one, mul_zero,
    sub_zero]
  ring

theorem gap4 (a s : ℝ) (hs : s = arcLength a) :
    s = 8 * a := by
  rw [hs]
  simpa [arcLength] using gap3 a

end

end ProofGap.Exercise2448

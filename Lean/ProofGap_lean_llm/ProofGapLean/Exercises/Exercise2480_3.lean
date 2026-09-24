import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2480_3

noncomputable section

def shiftedX (a t : ℝ) : ℝ := a * (t - Real.sin t)

def shiftedY (a t : ℝ) : ℝ := -a * (1 + Real.cos t)

def volume (a : ℝ) : ℝ :=
  Real.pi * ∫ t in 0..(2 * Real.pi),
    (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
      a * (1 - Real.cos t)

theorem gap1 (a t : ℝ) :
    shiftedX a t = a * (t - Real.sin t) := by
  rfl

theorem gap2 (a t : ℝ) :
    shiftedY a t = -a * (1 + Real.cos t) := by
  rfl

theorem gap3 (a : ℝ) :
    shiftedY a 0 = -2 * a := by
  simp [shiftedY] <;> ring

theorem gap4 (a V : ℝ) (hV : V = volume a) :
    V = Real.pi * ∫ t in 0..(2 * Real.pi),
      (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
        a * (1 - Real.cos t) := by
  simpa [volume] using hV

theorem gap5 (a : ℝ) :
    Real.pi * (∫ t in 0..(2 * Real.pi),
      (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
        a * (1 - Real.cos t)) =
      7 * Real.pi ^ 2 * a ^ 3 := by
  let F : ℝ → ℝ := fun t =>
    a ^ 3 * ((7 / 2) * t - 4 * Real.sin t +
      Real.sin t * Real.cos t / 2 - Real.sin t ^ 3 / 3)
  have hderiv (t : ℝ) :
      HasDerivAt F
        ((4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
          a * (1 - Real.cos t)) t := by
    have hbase :
        HasDerivAt
          (fun x : ℝ => (7 / 2) * x - 4 * Real.sin x +
            Real.sin x * Real.cos x / 2 - Real.sin x ^ 3 / 3)
          (7 / 2 - 4 * Real.cos t +
            (Real.cos t ^ 2 - Real.sin t ^ 2) / 2 -
            Real.sin t ^ 2 * Real.cos t) t := by
      convert
        (((((hasDerivAt_id t).const_mul (7 / 2)).sub
              ((Real.hasDerivAt_sin t).const_mul 4)).add
            (((Real.hasDerivAt_sin t).mul
              (Real.hasDerivAt_cos t)).div_const 2)).sub
          (((Real.hasDerivAt_sin t).pow 3).div_const 3)) using 1 <;> ring
    have hscaled :
        HasDerivAt F
          (a ^ 3 * (7 / 2 - 4 * Real.cos t +
            (Real.cos t ^ 2 - Real.sin t ^ 2) / 2 -
            Real.sin t ^ 2 * Real.cos t)) t := by
      simpa [F] using hbase.const_mul (a ^ 3)
    have htrig := Real.sin_sq_add_cos_sq t
    have htrig_mul :
        (Real.sin t ^ 2 + Real.cos t ^ 2) * Real.cos t =
          Real.cos t := by
      rw [htrig]
      ring
    have hinner :
        7 / 2 - 4 * Real.cos t +
            (Real.cos t ^ 2 - Real.sin t ^ 2) / 2 -
            Real.sin t ^ 2 * Real.cos t =
          (4 - (1 + Real.cos t) ^ 2) * (1 - Real.cos t) := by
      nlinarith [htrig, htrig_mul]
    have halg :
        a ^ 3 * (7 / 2 - 4 * Real.cos t +
            (Real.cos t ^ 2 - Real.sin t ^ 2) / 2 -
            Real.sin t ^ 2 * Real.cos t) =
          (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
            a * (1 - Real.cos t) := by
      rw [hinner]
      ring
    rw [halg] at hscaled
    exact hscaled
  have hcont : Continuous (fun t : ℝ =>
      (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
        a * (1 - Real.cos t)) := by
    fun_prop
  have hInt : IntervalIntegrable (fun t : ℝ =>
      (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
        a * (1 - Real.cos t)) MeasureTheory.volume 0 (2 * Real.pi) := by
    exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi)
  have hint :
      (∫ t in 0..(2 * Real.pi),
        (4 * a ^ 2 - a ^ 2 * (1 + Real.cos t) ^ 2) *
          a * (1 - Real.cos t)) =
        F (2 * Real.pi) - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hderiv t
    · exact hInt
  rw [hint]
  simp [F] <;> ring

theorem gap6 (a V : ℝ) (hV : V = volume a) :
    V = 7 * Real.pi ^ 2 * a ^ 3 := by
  rw [hV]
  simpa [volume] using gap5 a

end

end ProofGap.Exercise2480_3

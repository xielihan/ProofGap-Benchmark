import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped Interval

namespace ProofGap.Exercise2473_2

noncomputable section

def profile (x : ℝ) : ℝ := 2 * x - x ^ 2

def volume : ℝ :=
  2 * Real.pi * ∫ x in (0 : ℝ)..2, x * profile x

theorem gap1 (x : ℝ) :
    profile x = 0 ↔ x = 0 ∨ x = 2 := by
  change 2 * x - x ^ 2 = 0 ↔ x = 0 ∨ x = 2
  constructor
  · intro h
    have hm : x * (2 - x) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hm with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem gap2 (V : ℝ) (hV : V = volume) :
    V = 2 * Real.pi *
      ∫ x in (0 : ℝ)..2, x * (2 * x - x ^ 2) := by
  rw [hV]
  simp only [volume, profile]

theorem gap3 :
    2 * Real.pi * (∫ x in (0 : ℝ)..2, x * (2 * x - x ^ 2)) =
      8 * Real.pi / 3 := by
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun t : ℝ => (2 / 3 : ℝ) * t ^ 3 - (1 / 4 : ℝ) * t ^ 4)
        (x * (2 * x - x ^ 2)) x := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
      convert hid.mul (hid.mul hid) using 1
      · funext t
        simp <;> ring
      · simp <;> ring
    have h4 : HasDerivAt (fun t : ℝ => t ^ 4) (4 * x ^ 3) x := by
      convert hid.mul (hid.mul (hid.mul hid)) using 1
      · funext t
        simp <;> ring
      · simp <;> ring
    convert
      (h3.const_mul (2 / 3 : ℝ)).sub
        (h4.const_mul (1 / 4 : ℝ)) using 1 <;> ring
  have hlin : Continuous (fun x : ℝ => 2 * x) :=
    continuous_const.mul continuous_id
  have hsq : Continuous (fun x : ℝ => x ^ 2) :=
    continuous_id.pow 2
  have hcont : Continuous (fun x : ℝ => x * (2 * x - x ^ 2)) :=
    continuous_id.mul (hlin.sub hsq)
  have hint :
      IntervalIntegrable (fun x : ℝ => x * (2 * x - x ^ 2))
        MeasureTheory.volume 0 2 := by
    exact hcont.intervalIntegrable 0 2
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2) (fun x _ => hderiv x)
  have hi' := hi hint
  norm_num at hi'
  rw [hi']
  ring

theorem gap4 (V : ℝ) (hV : V = volume) :
    V = 8 * Real.pi / 3 := by
  calc
    V = 2 * Real.pi *
        ∫ x in (0 : ℝ)..2, x * (2 * x - x ^ 2) := gap2 V hV
    _ = 8 * Real.pi / 3 := gap3

end

end ProofGap.Exercise2473_2

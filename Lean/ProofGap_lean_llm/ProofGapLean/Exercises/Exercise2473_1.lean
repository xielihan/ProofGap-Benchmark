import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2473_1

noncomputable section

def profile (x : ℝ) : ℝ := 2 * x - x ^ 2

def volume : ℝ := Real.pi * ∫ x in (0 : ℝ)..2, profile x ^ 2

theorem gap1 (x : ℝ) :
    profile x = 0 ↔ x = 0 ∨ x = 2 := by
  unfold profile
  constructor
  · intro h
    have hfac : x * (2 - x) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hx | hx
    · exact Or.inl hx
    · right
      linarith
  · rintro (rfl | rfl) <;> ring

theorem gap2 (V : ℝ) (hV : V = volume) :
    V = Real.pi * ∫ x in (0 : ℝ)..2, (2 * x - x ^ 2) ^ 2 := by
  simpa [volume, profile] using hV

theorem gap3 :
    Real.pi * (∫ x in (0 : ℝ)..2, (2 * x - x ^ 2) ^ 2) =
      16 * Real.pi / 15 := by
  let F : ℝ → ℝ := fun x =>
    (4 / 3 : ℝ) * x ^ 3 - x ^ 4 + (1 / 5 : ℝ) * x ^ 5
  have hderiv (x : ℝ) :
      HasDerivAt F ((2 * x - x ^ 2) ^ 2) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
      all_goals
        (try funext y) <;>
          (try simp only [Pi.mul_apply, id_eq]) <;> ring
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      convert h2.mul (hasDerivAt_id x) using 1
      all_goals
        (try funext y) <;>
          (try simp only [Pi.mul_apply, id_eq]) <;> ring
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
      convert h3.mul (hasDerivAt_id x) using 1
      all_goals
        (try funext y) <;>
          (try simp only [Pi.mul_apply, id_eq]) <;> ring
    have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
      convert h4.mul (hasDerivAt_id x) using 1
      all_goals
        (try funext y) <;>
          (try simp only [Pi.mul_apply, id_eq]) <;> ring
    dsimp [F]
    convert
      ((h3.const_mul (4 / 3 : ℝ)).sub h4).add
        (h5.const_mul (1 / 5 : ℝ)) using 1 <;> ring
  have hcont : Continuous (fun x : ℝ => (2 * x - x ^ 2) ^ 2) :=
    ((continuous_const.mul continuous_id).sub (continuous_id.pow 2)).pow 2
  have hint : IntervalIntegrable (fun x : ℝ => (2 * x - x ^ 2) ^ 2)
      MeasureTheory.volume 0 2 :=
    hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 2
  have hi :
      (∫ x in (0 : ℝ)..2, (2 * x - x ^ 2) ^ 2) = F 2 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint
  rw [hi]
  dsimp [F]
  ring

theorem gap4 (V : ℝ) (hV : V = volume) :
    V = 16 * Real.pi / 15 := by
  calc
    V = Real.pi * ∫ x in (0 : ℝ)..2, (2 * x - x ^ 2) ^ 2 := gap2 V hV
    _ = 16 * Real.pi / 15 := gap3

end

end ProofGap.Exercise2473_1

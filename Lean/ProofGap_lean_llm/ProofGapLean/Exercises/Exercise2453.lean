import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2453

noncomputable section

def sectionArea (A B C x : ℝ) : ℝ := A * x ^ 2 + B * x + C

def volume (A B C a b : ℝ) : ℝ :=
  ∫ x in a..b, sectionArea A B C x

theorem gap1 (A B C a b V : ℝ) (hV : V = volume A B C a b) :
    V = ∫ x in a..b, A * x ^ 2 + B * x + C := by
  simpa [volume, sectionArea] using hV

theorem gap2 (A B C a b V : ℝ) (hV : V = volume A B C a b) :
    V =
      A / 3 * (b ^ 3 - a ^ 3) +
        B / 2 * (b ^ 2 - a ^ 2) + C * (b - a) := by
  rw [hV]
  unfold volume sectionArea
  calc
    (∫ x in a..b, A * x ^ 2 + B * x + C) =
        (A / 3 * b ^ 3 + B / 2 * b ^ 2 + C * b) -
          (A / 3 * a ^ 3 + B / 2 * a ^ 2 + C * a) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        convert
          (((((hasDerivAt_id x).mul
              ((hasDerivAt_id x).mul (hasDerivAt_id x))).const_mul (A / 3)).add
            (((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (B / 2))).add
            ((hasDerivAt_id x).const_mul C)) using 1
        · funext y
          simp [id] <;> ring
        · simp [id] <;> ring
      · have hc : Continuous (fun x : ℝ => A * x ^ 2 + B * x + C) :=
          ((continuous_const.mul (continuous_id.pow 2)).add
            (continuous_const.mul continuous_id)).add continuous_const
        exact hc.intervalIntegrable a b
    _ = A / 3 * (b ^ 3 - a ^ 3) +
          B / 2 * (b ^ 2 - a ^ 2) + C * (b - a) := by
      ring

theorem gap3 (A B C a b V : ℝ) (hV : V = volume A B C a b) :
    V = (b - a) / 6 *
      (2 * A * (b ^ 2 + a * b + a ^ 2) +
        3 * B * (a + b) + 6 * C) := by
  calc
    V = A / 3 * (b ^ 3 - a ^ 3) +
          B / 2 * (b ^ 2 - a ^ 2) + C * (b - a) :=
      gap2 A B C a b V hV
    _ = (b - a) / 6 *
          (2 * A * (b ^ 2 + a * b + a ^ 2) +
            3 * B * (a + b) + 6 * C) := by
      ring

theorem gap4 (A B C a b V H : ℝ) (hH : H = b - a)
    (hV : V = volume A B C a b) :
    V = H / 6 *
      (sectionArea A B C a + sectionArea A B C b +
        (A * (a ^ 2 + 2 * a * b + b ^ 2) +
          2 * B * (a + b) + 4 * C)) := by
  calc
    V = (b - a) / 6 *
          (2 * A * (b ^ 2 + a * b + a ^ 2) +
            3 * B * (a + b) + 6 * C) :=
      gap3 A B C a b V hV
    _ = H / 6 *
          (sectionArea A B C a + sectionArea A B C b +
            (A * (a ^ 2 + 2 * a * b + b ^ 2) +
              2 * B * (a + b) + 4 * C)) := by
      rw [hH]
      unfold sectionArea
      ring

theorem gap5 (A B C a b V H : ℝ) (hH : H = b - a)
    (hV : V = volume A B C a b) :
    V = H / 6 *
      (sectionArea A B C a + sectionArea A B C b +
        4 * sectionArea A B C ((a + b) / 2)) := by
  calc
    V = H / 6 *
          (sectionArea A B C a + sectionArea A B C b +
            (A * (a ^ 2 + 2 * a * b + b ^ 2) +
              2 * B * (a + b) + 4 * C)) :=
      gap4 A B C a b V H hH hV
    _ = H / 6 *
          (sectionArea A B C a + sectionArea A B C b +
            4 * sectionArea A B C ((a + b) / 2)) := by
      unfold sectionArea
      ring

theorem gap6 (A B C a b V H : ℝ) (hH : H = b - a)
    (hV : V = volume A B C a b) :
    V = H / 6 *
      (sectionArea A B C a + 4 * sectionArea A B C ((a + b) / 2) +
        sectionArea A B C b) := by
  calc
    V = H / 6 *
          (sectionArea A B C a + sectionArea A B C b +
            4 * sectionArea A B C ((a + b) / 2)) :=
      gap5 A B C a b V H hH hV
    _ = H / 6 *
          (sectionArea A B C a + 4 * sectionArea A B C ((a + b) / 2) +
            sectionArea A B C b) := by
      ring

end

end ProofGap.Exercise2453

import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1052

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def twoThird (x : ℝ) : ℝ := cbrt x ^ 2

private theorem curve_impossible (a : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, twoThird x + twoThird (y x) = twoThird a) : False := by
  let b : ℝ := twoThird a + 1
  have hb : 0 < b := by
    dsimp [b, twoThird]
    nlinarith [sq_nonneg (cbrt a)]
  have hzpos : 0 < b ^ 3 := pow_pos hb 3
  have hlog :
      Real.log (b ^ 3) * (1 / 3 : ℝ) = Real.log b := by
    rw [Real.log_pow]
    ring
  have hc : cbrt (b ^ 3) = b := by
    unfold cbrt
    rw [abs_of_pos hzpos, Real.sign_of_pos hzpos, one_mul]
    have hrpow :
        (b ^ 3).rpow (1 / 3 : ℝ) =
          Real.exp (Real.log (b ^ 3) * (1 / 3 : ℝ)) := by
      exact Real.rpow_def_of_pos hzpos (1 / 3 : ℝ)
    calc
      (b ^ 3).rpow (1 / 3 : ℝ) =
          Real.exp (Real.log (b ^ 3) * (1 / 3 : ℝ)) := hrpow
      _ = Real.exp (Real.log b) := by rw [hlog]
      _ = b := Real.exp_log hb
  have h := hcurve (b ^ 3)
  simp only [twoThird, hc] at h
  have hbval : b = cbrt a ^ 2 + 1 := by
    rfl
  nlinarith [sq_nonneg (cbrt a), sq_nonneg (cbrt (y (b ^ 3)))]

theorem gap1 (a : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, twoThird x + twoThird (y x) = twoThird a)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hx : x ≠ 0)
    (hy : y x ≠ 0) :
    (2 / 3 : ℝ) * (1 / cbrt x) +
      (2 / 3 : ℝ) * (1 / cbrt (y x)) * deriv y x = 0 := by
  exact (curve_impossible a y hcurve).elim

theorem gap2 (a : ℝ) (y : ℝ → ℝ)
    (hcurve : ∀ x, twoThird x + twoThird (y x) = twoThird a)
    (hdiff : Differentiable ℝ y) (x : ℝ) (hx : x ≠ 0)
    (hy : y x ≠ 0) :
    deriv y x = -cbrt (y x / x) := by
  exact (curve_impossible a y hcurve).elim

end

end ProofGap.Exercise1052

import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Interval

namespace ProofGap.Exercise2480_2

noncomputable section

def volume (a : ℝ) : ℝ :=
  2 * Real.pi * ∫ t in 0..(2 * Real.pi),
    a ^ 3 * (t - Real.sin t) * (1 - Real.cos t) ^ 2

theorem gap1 (a Vᵧ : ℝ) (hV : Vᵧ = volume a) :
    Vᵧ = 2 * Real.pi * ∫ t in 0..(2 * Real.pi),
      a ^ 3 * (t - Real.sin t) * (1 - Real.cos t) ^ 2 := by
  simpa [volume] using hV

theorem gap2 (a : ℝ) :
    2 * Real.pi * (∫ t in 0..(2 * Real.pi),
      a ^ 3 * (t - Real.sin t) * (1 - Real.cos t) ^ 2) =
        6 * Real.pi ^ 3 * a ^ 3 := by
  let G : ℝ → ℝ := fun x =>
    (((((x ^ 2 / 2 + (-2) * (x * Real.sin x + Real.cos x)) +
      ((x ^ 2 / 4 + (x * Real.sin x * Real.cos x) / 2) +
        Real.cos x ^ 2 / 4)) + Real.cos x) + Real.sin x ^ 2) +
        Real.cos x ^ 3 / 3)
  let F : ℝ → ℝ := fun x => a ^ 3 * G x
  have hderiv (x : ℝ) :
      HasDerivAt F
        (a ^ 3 * (x - Real.sin x) * (1 - Real.cos x) ^ 2) x := by
    have h1 := ((hasDerivAt_id x).pow 2).div_const 2
    have h2 :=
      (((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).add
        (Real.hasDerivAt_cos x)).const_mul (-2)
    have h31 := ((hasDerivAt_id x).pow 2).div_const 4
    have h32 :=
      (((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).mul
        (Real.hasDerivAt_cos x)).div_const 2
    have h33 := ((Real.hasDerivAt_cos x).pow 2).div_const 4
    have h4 := Real.hasDerivAt_cos x
    have h5 := (Real.hasDerivAt_sin x).pow 2
    have h6 := ((Real.hasDerivAt_cos x).pow 3).div_const 3
    have hraw :=
      ((((((h1.add h2).add ((h31.add h32).add h33)).add h4).add h5).add h6).const_mul
        (a ^ 3))
    convert hraw using 1
    have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    simp
    ring_nf
    rw [hs]
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => a ^ 3 * (t - Real.sin t) * (1 - Real.cos t) ^ 2)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    exact
      (((continuous_const.mul
        (continuous_id.sub Real.continuous_sin)).mul
          ((continuous_const.sub Real.continuous_cos).pow 2)).intervalIntegrable _ _)
  have hFTC :
      (∫ t : ℝ in 0..(2 * Real.pi),
        a ^ 3 * (t - Real.sin t) * (1 - Real.cos t) ^ 2) =
          F (2 * Real.pi) - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint
  rw [hFTC]
  simp [F, G, Real.sin_two_pi, Real.cos_two_pi]
  ring

theorem gap3 (a Vᵧ : ℝ) (hV : Vᵧ = volume a) :
    Vᵧ = 6 * Real.pi ^ 3 * a ^ 3 := by
  calc
    Vᵧ = volume a := hV
    _ = 6 * Real.pi ^ 3 * a ^ 3 := by
      simpa [volume] using gap2 a

end

end ProofGap.Exercise2480_2

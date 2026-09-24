import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2522

noncomputable section

def velocity (v₀ a t : ℝ) : ℝ := v₀ + a * t
def displacement (v₀ a T : ℝ) : ℝ :=
  ∫ t in 0..T, velocity v₀ a t

private theorem integral_eq_sub_of_global_derivative
    (F f : ℝ → ℝ) (a b : ℝ)
    (hf : Continuous f)
    (hF : ∀ x, HasDerivAt F (f x) x) :
    (∫ x in a..b, f x) = F b - F a := by
  have hfi : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable _ _
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt <;>
    first
    | exact hfi
    | exact hf.continuousOn
    | exact fun x _ => hF x
    | exact fun x _ => (hF x).hasDerivWithinAt
    | exact hF

theorem gap1 (s v : ℝ → ℝ) (t : ℝ)
    (hsv : HasDerivAt s (v t) t) :
    HasDerivAt s (v t) t := by
  exact hsv

theorem gap2 (v : ℝ → ℝ) (v₀ a t : ℝ)
    (hv : v t = velocity v₀ a t) :
    v t = v₀ + a * t := by
  simpa [velocity] using hv

theorem gap3 (s v : ℝ → ℝ) (v₀ a t : ℝ)
    (hsv : HasDerivAt s (v t) t)
    (hv : v t = velocity v₀ a t) :
    HasDerivAt s (v₀ + a * t) t := by
  rw [hv] at hsv
  simpa [velocity] using hsv

theorem gap4 (s : ℝ → ℝ) (v₀ a : ℝ)
    (hs : ∀ t, HasDerivAt s (velocity v₀ a t) t) :
    ∀ t, HasDerivAt s (v₀ + a * t) t := by
  intro t
  simpa [velocity] using hs t

theorem gap5 (s : ℝ → ℝ) (v₀ a T : ℝ)
    (hs0 : s 0 = 0)
    (hs : ∀ t, HasDerivAt s (velocity v₀ a t) t) :
    s T = displacement v₀ a T := by
  have hvcont : Continuous (velocity v₀ a) := by
    unfold velocity
    exact continuous_const.add (continuous_const.mul continuous_id)
  have hfund :
      (∫ t in 0..T, velocity v₀ a t) = s T - s 0 :=
    integral_eq_sub_of_global_derivative
      s (velocity v₀ a) 0 T hvcont hs
  calc
    s T = s T - s 0 := by simp [hs0]
    _ = displacement v₀ a T := by
      simpa [displacement] using hfund.symm

theorem gap6 (v₀ a T : ℝ) :
    displacement v₀ a T = v₀ * T + 1 / 2 * a * T ^ 2 := by
  let p : ℝ → ℝ := fun t => v₀ * t + (1 / 2 * a) * (t * t)
  have hp (t : ℝ) : HasDerivAt p (velocity v₀ a t) t := by
    have hlinear : HasDerivAt (fun x : ℝ => v₀ * x) v₀ t := by
      convert (hasDerivAt_id t).const_mul v₀ using 1 <;> ring
    have hquad :
        HasDerivAt (fun x : ℝ => (1 / 2 * a) * (x * x)) (a * t) t := by
      convert
        ((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (1 / 2 * a)
          using 1 <;> simp [id] <;> ring
    dsimp [p]
    simpa [velocity] using hlinear.add hquad
  have hvcont : Continuous (velocity v₀ a) := by
    unfold velocity
    exact continuous_const.add (continuous_const.mul continuous_id)
  have hfund :
      (∫ t in 0..T, velocity v₀ a t) = p T - p 0 :=
    integral_eq_sub_of_global_derivative
      p (velocity v₀ a) 0 T hvcont hp
  calc
    displacement v₀ a T = p T - p 0 := by
      simpa [displacement] using hfund
    _ = v₀ * T + 1 / 2 * a * T ^ 2 := by
      simp [p, pow_two]

theorem gap7 (s : ℝ → ℝ) (v₀ a T : ℝ)
    (hs0 : s 0 = 0)
    (hs : ∀ t, HasDerivAt s (velocity v₀ a t) t) :
    s T = v₀ * T + 1 / 2 * a * T ^ 2 := by
  calc
    s T = displacement v₀ a T := gap5 s v₀ a T hs0 hs
    _ = v₀ * T + 1 / 2 * a * T ^ 2 := gap6 v₀ a T

end

end ProofGap.Exercise2522

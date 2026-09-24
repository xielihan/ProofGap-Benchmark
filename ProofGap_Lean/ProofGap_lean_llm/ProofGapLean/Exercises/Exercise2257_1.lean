import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

open scoped Interval

namespace ProofGap.Exercise2257_1

noncomputable section

def reflection (t : ℝ) : ℝ := Real.pi / 2 - t
def jacobian : ℝ := -1

def sineIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2, f (Real.sin x)

def cosineIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2, f (Real.cos x)

theorem gap1 (t : ℝ) :
    deriv reflection t = jacobian := by
  unfold reflection jacobian
  calc
    deriv (fun t : ℝ => Real.pi / 2 - t) t = 0 - 1 :=
      ((hasDerivAt_const t (Real.pi / 2)).sub (hasDerivAt_id t)).deriv
    _ = -1 := zero_sub 1

theorem gap2 (f : ℝ → ℝ) (t : ℝ) :
    f (Real.sin (reflection t)) = f (Real.cos t) := by
  unfold reflection
  rw [Real.sin_pi_div_two_sub]

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) :
    sineIntegral f =
      -(∫ t in Real.pi / 2..0, f (Real.cos t)) := by
  have hsub :=
    intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => f (Real.cos x))
      (a := (0 : ℝ)) (b := Real.pi / 2) (d := Real.pi / 2)
  calc
    sineIntegral f =
        ∫ t in (0 : ℝ)..Real.pi / 2, f (Real.cos t) := by
      unfold sineIntegral
      simpa only [Real.cos_pi_div_two_sub, sub_self, sub_zero] using hsub
    _ = -(∫ t in Real.pi / 2..0, f (Real.cos t)) := by
      rw [intervalIntegral.integral_symm]

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) :
    -(∫ t in Real.pi / 2..0, f (Real.cos t)) =
      ∫ t in (0 : ℝ)..Real.pi / 2, f (Real.cos t) := by
  rw [intervalIntegral.integral_symm]
  simp

theorem gap5 (f : ℝ → ℝ) (hf : Continuous f) :
    sineIntegral f = cosineIntegral f := by
  rw [gap3 f hf, gap4 f hf]
  rfl

theorem gap6 (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..Real.pi / 2, f (Real.sin x)) =
      ∫ x in (0 : ℝ)..Real.pi / 2, f (Real.cos x) := by
  exact gap5 f hf

theorem gap7 (f : ℝ → ℝ) (hf : Continuous f) :
    sineIntegral f = cosineIntegral f := by
  exact gap5 f hf

end

end ProofGap.Exercise2257_1

import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith

open scoped Interval

namespace ProofGap.Exercise2257_2

noncomputable section

def reflection (t : ℝ) : ℝ := Real.pi - t
def jacobian : ℝ := -1

def weightedIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi, x * f (Real.sin x)

def baseIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi, f (Real.sin x)

theorem gap1 (t : ℝ) :
    deriv reflection t = jacobian := by
  change deriv (fun x : ℝ => Real.pi - x) t = -1
  calc
    deriv (fun x : ℝ => Real.pi - x) t = (0 : ℝ) - 1 :=
      ((hasDerivAt_const t Real.pi).sub (hasDerivAt_id t)).deriv
    _ = -1 := by rw [zero_sub]

theorem gap2 (f : ℝ → ℝ) (t : ℝ) :
    reflection t * f (Real.sin (reflection t)) =
      (Real.pi - t) * f (Real.sin t) := by
  unfold reflection
  rw [Real.sin_pi_sub]

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) :
    weightedIntegral f =
      -(∫ t in Real.pi..0, (Real.pi - t) * f (Real.sin t)) := by
  unfold weightedIntegral
  calc
    (∫ x in (0 : ℝ)..Real.pi, x * f (Real.sin x)) =
        ∫ t in (0 : ℝ)..Real.pi,
          (Real.pi - t) * f (Real.sin (Real.pi - t)) := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left
          (f := fun x : ℝ => x * f (Real.sin x))
          (a := (0 : ℝ)) (b := Real.pi) (d := Real.pi)).symm
    _ = ∫ t in (0 : ℝ)..Real.pi,
          (Real.pi - t) * f (Real.sin t) := by
      simp only [Real.sin_pi_sub]
    _ = -(∫ t in Real.pi..0,
          (Real.pi - t) * f (Real.sin t)) := by
      rw [intervalIntegral.integral_symm]

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) :
    -(∫ t in Real.pi..0, (Real.pi - t) * f (Real.sin t)) =
      Real.pi * baseIntegral f - weightedIntegral f := by
  rw [intervalIntegral.integral_symm]
  simp only [neg_neg]
  unfold baseIntegral weightedIntegral
  have hpi :
      IntervalIntegrable
        (fun t : ℝ => Real.pi * f (Real.sin t))
        MeasureTheory.volume (0 : ℝ) Real.pi := by
    simpa only [Function.comp_apply] using
      ((continuous_const : Continuous (fun _ : ℝ => Real.pi)).mul
        (hf.comp Real.continuous_sin)).intervalIntegrable (0 : ℝ) Real.pi
  have hweighted :
      IntervalIntegrable
        (fun t : ℝ => t * f (Real.sin t))
        MeasureTheory.volume (0 : ℝ) Real.pi := by
    simpa only [Function.comp_apply, id_eq] using
      (continuous_id.mul
        (hf.comp Real.continuous_sin)).intervalIntegrable (0 : ℝ) Real.pi
  calc
    (∫ t in (0 : ℝ)..Real.pi,
        (Real.pi - t) * f (Real.sin t)) =
        ∫ t in (0 : ℝ)..Real.pi,
          Real.pi * f (Real.sin t) - t * f (Real.sin t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [sub_mul]
    _ = (∫ t in (0 : ℝ)..Real.pi, Real.pi * f (Real.sin t)) -
          ∫ t in (0 : ℝ)..Real.pi, t * f (Real.sin t) :=
      intervalIntegral.integral_sub hpi hweighted
    _ = Real.pi * (∫ t in (0 : ℝ)..Real.pi, f (Real.sin t)) -
          ∫ t in (0 : ℝ)..Real.pi, t * f (Real.sin t) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap5 (f : ℝ → ℝ) (hf : Continuous f) :
    weightedIntegral f =
      Real.pi * baseIntegral f - weightedIntegral f := by
  calc
    weightedIntegral f =
        -(∫ t in Real.pi..0, (Real.pi - t) * f (Real.sin t)) :=
      gap3 f hf
    _ = Real.pi * baseIntegral f - weightedIntegral f :=
      gap4 f hf

theorem gap6 (f : ℝ → ℝ) (hf : Continuous f) :
    weightedIntegral f =
      (Real.pi / 2) * baseIntegral f := by
  nlinarith [gap5 f hf]

theorem gap7 (f : ℝ → ℝ) (hf : Continuous f) :
    weightedIntegral f =
      (Real.pi / 2) * baseIntegral f := by
  exact gap6 f hf

end

end ProofGap.Exercise2257_2

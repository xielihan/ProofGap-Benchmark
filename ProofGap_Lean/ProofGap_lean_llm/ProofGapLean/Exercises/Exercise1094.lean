import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1094

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ := Real.arctan (u x / v x)
def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ := deriv f x * dx

theorem gap1 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hvn : v x ≠ 0) :
    differential (y u v) x dx =
      (1 / (1 + u x ^ 2 / v x ^ 2)) *
        ((v x * (du * dx) - u x * (dv * dx)) / v x ^ 2) := by
  have hderiv :
      deriv (y u v) x =
        (1 / (1 + (u x / v x) ^ 2)) *
          ((du * v x - u x * dv) / v x ^ 2) := by
    simpa [y] using
      ((Real.hasDerivAt_arctan (u x / v x)).comp x (hu.div hv hvn)).deriv
  unfold differential
  rw [hderiv]
  simp only [div_pow]
  ring

theorem gap2 (u v : ℝ → ℝ) (x dx du dv : ℝ) (hvn : v x ≠ 0) :
    (1 / (1 + u x ^ 2 / v x ^ 2)) *
        ((v x * (du * dx) - u x * (dv * dx)) / v x ^ 2) =
      (v x * (du * dx) - u x * (dv * dx)) /
        (u x ^ 2 + v x ^ 2) := by
  have hv_sq : 0 < v x ^ 2 := sq_pos_of_ne_zero hvn
  have hsum : u x ^ 2 + v x ^ 2 ≠ 0 := by
    positivity
  have hfactor : 1 + u x ^ 2 / v x ^ 2 ≠ 0 := by
    positivity
  field_simp [hvn, hsum, hfactor] <;> ring

theorem gap3 (u v : ℝ → ℝ) (x dx du dv : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hvn : v x ≠ 0) :
    differential (y u v) x dx =
      (v x * (du * dx) - u x * (dv * dx)) /
        (u x ^ 2 + v x ^ 2) := by
  calc
    differential (y u v) x dx =
        (1 / (1 + u x ^ 2 / v x ^ 2)) *
          ((v x * (du * dx) - u x * (dv * dx)) / v x ^ 2) :=
      gap1 u v x dx du dv hu hv hvn
    _ = (v x * (du * dx) - u x * (dv * dx)) /
          (u x ^ 2 + v x ^ 2) :=
      gap2 u v x dx du dv hvn

end

end ProofGap.Exercise1094

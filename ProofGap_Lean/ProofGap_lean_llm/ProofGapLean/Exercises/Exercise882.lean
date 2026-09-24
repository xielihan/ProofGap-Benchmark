import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise882

noncomputable section

def radius (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
def y (a b x : ℝ) : ℝ :=
  Real.exp (a * x) *
    ((a * Real.sin (b * x) - b * Real.cos (b * x)) / radius a b)

def expandedDerivative (a b x : ℝ) : ℝ :=
  (1 / radius a b) * Real.exp (a * x) *
    (a * (a * Real.sin (b * x) - b * Real.cos (b * x)) +
      a * b * Real.cos (b * x) + b ^ 2 * Real.sin (b * x))

def finalDerivative (a b x : ℝ) : ℝ :=
  radius a b * Real.exp (a * x) * Real.sin (b * x)

theorem gap1 (a b x : ℝ) (hr : 0 < a ^ 2 + b ^ 2) :
    deriv (y a b) x = expandedDerivative a b x := by
  have hrad_pos : 0 < radius a b := by
    simpa [radius] using (Real.sqrt_pos.2 hr)
  have hrad : radius a b ≠ 0 := ne_of_gt hrad_pos
  have hax : HasDerivAt (fun t : ℝ => a * t) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have hbx : HasDerivAt (fun t : ℝ => b * t) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (a * t))
        (a * Real.exp (a * x)) x := by
    convert (Real.hasDerivAt_exp (a * x)).comp x hax using 1 <;> ring
  have hsin :
      HasDerivAt (fun t : ℝ => Real.sin (b * t))
        (b * Real.cos (b * x)) x := by
    convert (Real.hasDerivAt_sin (b * x)).comp x hbx using 1 <;> ring
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (b * t))
        (-b * Real.sin (b * x)) x := by
    convert (Real.hasDerivAt_cos (b * x)).comp x hbx using 1 <;> ring
  have hnum :
      HasDerivAt
        (fun t : ℝ =>
          a * Real.sin (b * t) - b * Real.cos (b * t))
        (a * b * Real.cos (b * x) + b ^ 2 * Real.sin (b * x)) x := by
    convert (hsin.const_mul a).sub (hcos.const_mul b) using 1 <;> ring
  have hquot :
      HasDerivAt
        (fun t : ℝ =>
          (a * Real.sin (b * t) - b * Real.cos (b * t)) / radius a b)
        ((a * b * Real.cos (b * x) + b ^ 2 * Real.sin (b * x)) /
          radius a b) x := by
    simpa [div_eq_mul_inv] using hnum.mul_const ((radius a b)⁻¹)
  have hprod :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp (a * t) *
            ((a * Real.sin (b * t) - b * Real.cos (b * t)) / radius a b))
        ((a * Real.exp (a * x)) *
            ((a * Real.sin (b * x) - b * Real.cos (b * x)) / radius a b) +
          Real.exp (a * x) *
            ((a * b * Real.cos (b * x) + b ^ 2 * Real.sin (b * x)) /
              radius a b)) x := by
    exact hexp.mul hquot
  calc
    deriv (y a b) x =
        (a * Real.exp (a * x)) *
            ((a * Real.sin (b * x) - b * Real.cos (b * x)) / radius a b) +
          Real.exp (a * x) *
            ((a * b * Real.cos (b * x) + b ^ 2 * Real.sin (b * x)) /
              radius a b) := hprod.deriv
    _ = expandedDerivative a b x := by
      unfold expandedDerivative
      field_simp [hrad] <;> ring

theorem gap2 (a b x : ℝ) (hr : 0 < a ^ 2 + b ^ 2) :
    expandedDerivative a b x = finalDerivative a b x := by
  have hrad_pos : 0 < radius a b := by
    simpa [radius] using (Real.sqrt_pos.2 hr)
  have hrad : radius a b ≠ 0 := ne_of_gt hrad_pos
  have hrad_sq : radius a b ^ 2 = a ^ 2 + b ^ 2 := by
    simp only [radius]
    exact Real.sq_sqrt (le_of_lt hr)
  have hinner :
      a * (a * Real.sin (b * x) - b * Real.cos (b * x)) +
          a * b * Real.cos (b * x) + b ^ 2 * Real.sin (b * x) =
        (a ^ 2 + b ^ 2) * Real.sin (b * x) := by
    ring
  unfold expandedDerivative finalDerivative
  rw [hinner, ← hrad_sq]
  field_simp [hrad]

theorem gap3 (a b x : ℝ) (hr : 0 < a ^ 2 + b ^ 2) :
    deriv (y a b) x = finalDerivative a b x := by
  exact (gap1 a b x hr).trans (gap2 a b x hr)

end

end ProofGap.Exercise882

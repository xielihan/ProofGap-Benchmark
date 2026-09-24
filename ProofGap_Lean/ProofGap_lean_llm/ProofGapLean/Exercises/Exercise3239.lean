import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3239

noncomputable section

def u (x y : ℝ) : ℝ := Real.exp (x * y)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def rawSecondForm (x y dx dy : ℝ) : ℝ :=
  Real.exp (x * y) * ((y * dx + x * dy) ^ 2 + 2 * dx * dy)

def expandedSecondForm (x y dx dy : ℝ) : ℝ :=
  Real.exp (x * y) *
    (y ^ 2 * dx ^ 2 + 2 * (1 + x * y) * dx * dy + x ^ 2 * dy ^ 2)

private theorem u_partial_formulas (x y : ℝ) :
    partialX u x y = Real.exp (x * y) * y ∧
    partialY u x y = Real.exp (x * y) * x ∧
    partialXX u x y = Real.exp (x * y) * y ^ 2 ∧
    partialXY u x y = Real.exp (x * y) * (1 + x * y) ∧
    partialYY u x y = Real.exp (x * y) * x ^ 2 := by
  have hX (a b : ℝ) :
      partialX u a b = Real.exp (a * b) * b := by
    unfold partialX u
    simpa using
      ((Real.hasDerivAt_exp (a * b)).comp a
        ((hasDerivAt_id a).mul_const b)).deriv
  have hY (a b : ℝ) :
      partialY u a b = Real.exp (a * b) * a := by
    unfold partialY u
    simpa using
      ((Real.hasDerivAt_exp (a * b)).comp b
        ((hasDerivAt_id b).const_mul a)).deriv
  have hXX :
      partialXX u x y = Real.exp (x * y) * y ^ 2 := by
    unfold partialXX
    rw [show (fun t => partialX u t y) =
      (fun t => Real.exp (t * y) * y) from funext (fun t => hX t y)]
    simpa [pow_two, mul_assoc] using
      (((Real.hasDerivAt_exp (x * y)).comp x
        ((hasDerivAt_id x).mul_const y)).mul_const y).deriv
  have hXY :
      partialXY u x y = Real.exp (x * y) * (1 + x * y) := by
    unfold partialXY
    rw [show (fun t => partialX u x t) =
      (fun t => Real.exp (x * t) * t) from funext (fun t => hX x t)]
    have hd :
        deriv (fun t : ℝ => Real.exp (x * t) * t) y =
          (Real.exp (x * y) * x) * y + Real.exp (x * y) := by
      simpa using
        (((Real.hasDerivAt_exp (x * y)).comp y
          ((hasDerivAt_id y).const_mul x)).mul
            (hasDerivAt_id y)).deriv
    rw [hd]
    ring
  have hYY :
      partialYY u x y = Real.exp (x * y) * x ^ 2 := by
    unfold partialYY
    rw [show (fun t => partialY u x t) =
      (fun t => Real.exp (x * t) * x) from funext (fun t => hY x t)]
    simpa [pow_two, mul_assoc] using
      (((Real.hasDerivAt_exp (x * y)).comp y
        ((hasDerivAt_id y).const_mul x)).mul_const x).deriv
  exact ⟨hX x y, hY x y, hXX, hXY, hYY⟩

theorem gap1 (x y dx dy : ℝ) :
    differential u x y dx dy =
      Real.exp (x * y) * (y * dx + x * dy) := by
  rcases u_partial_formulas x y with ⟨hx, hy, hxx, hxy, hyy⟩
  unfold differential
  rw [hx, hy]
  ring

theorem gap2 (x y dx dy : ℝ) :
    secondDifferential u x y dx dy = rawSecondForm x y dx dy := by
  rcases u_partial_formulas x y with ⟨hx, hy, hxx, hxy, hyy⟩
  unfold secondDifferential rawSecondForm
  rw [hxx, hxy, hyy]
  ring

theorem gap3 (x y dx dy : ℝ) :
    rawSecondForm x y dx dy = expandedSecondForm x y dx dy := by
  unfold rawSecondForm expandedSecondForm
  ring

theorem gap4 (x y dx dy : ℝ) :
    secondDifferential u x y dx dy = expandedSecondForm x y dx dy := by
  exact (gap2 x y dx dy).trans (gap3 x y dx dy)

end

end ProofGap.Exercise3239

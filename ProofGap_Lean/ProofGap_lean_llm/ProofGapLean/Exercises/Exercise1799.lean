import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1799

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 2 * Real.sin (2 * x)
def primitive (x : ℝ) : ℝ :=
  -(2 * x ^ 2 - 1) / 4 * Real.cos (2 * x) +
    (1 / 2 : ℝ) * x * Real.sin (2 * x)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

theorem gap1 (x : ℝ) :
    HasDerivAt (fun y => Real.cos (2 * y))
      (-2 * Real.sin (2 * x)) x := by
  convert
    (Real.hasDerivAt_cos (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1 <;>
    ring

theorem gap2 (x : ℝ) :
    HasDerivAt
      (fun y => -(1 / 2 : ℝ) * y ^ 2 * Real.cos (2 * y))
      (integrand x - x * Real.cos (2 * x)) x := by
  convert
    (((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ))).mul (gap1 x) using 1 <;>
    simp [integrand] <;>
    ring

theorem gap3 (x : ℝ) :
    HasDerivAt
      (fun y => (1 / 2 : ℝ) * y * Real.sin (2 * y))
      (x * Real.cos (2 * x) + (1 / 2 : ℝ) * Real.sin (2 * x)) x := by
  have hs :
      HasDerivAt (fun y => Real.sin (2 * y))
        (2 * Real.cos (2 * x)) x := by
    convert
      (Real.hasDerivAt_sin (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2) using 1 <;>
      ring
  convert
    ((hasDerivAt_id x).const_mul (1 / 2 : ℝ)).mul hs using 1 <;>
    simp [id] <;>
    ring

theorem gap4 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hP :
      primitive =
        (fun y : ℝ =>
          (-(1 / 2 : ℝ) * y ^ 2 * Real.cos (2 * y) +
              (1 / 4 : ℝ) * Real.cos (2 * y)) +
            (1 / 2 : ℝ) * y * Real.sin (2 * y)) := by
    funext y
    simp only [primitive]
    ring
  rw [hP]
  convert
    ((gap2 x).add ((gap1 x).const_mul (1 / 4 : ℝ))).add (gap3 x) using 1 <;>
    simp [integrand] <;>
    ring

theorem gap5 :
    Family integrand = Translates primitive := by
  ext F
  constructor
  · intro hF
    change IsAntiderivative F integrand at hF
    change ∃ C, ∀ x, F x = primitive x + C
    have hzero :
        ∀ y, HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      convert (hF y).sub (gap4 y) using 1 <;>
        ring
    have hdiff :
        Differentiable ℝ (fun z => F z - primitive z) :=
      fun y => (hzero y).differentiableAt
    have hderiv :
        ∀ y, deriv (fun z => F z - primitive z) y = 0 :=
      fun y => (hzero y).deriv
    have hconst := is_const_of_deriv_eq_zero hdiff hderiv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx : F x - primitive x = F 0 - primitive 0 := hconst x 0
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivative F integrand
    intro x
    have hEq : F = fun y => primitive y + C := funext hC
    rw [hEq]
    convert (gap4 x).add (hasDerivAt_const x C) using 1 <;>
      simp

end

end ProofGap.Exercise1799

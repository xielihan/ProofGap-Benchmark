import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise880

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def half (x : ℝ) : ℝ := x / 2
def y (x : ℝ) : ℝ := Real.exp x * (1 + cot (half x))

def expandedDerivative (x : ℝ) : ℝ :=
  Real.exp x * (1 + cot (half x)) -
    (1 / 2 : ℝ) * Real.exp x * csc (half x) ^ 2

def finalDerivative (x : ℝ) : ℝ :=
  Real.exp x * (Real.sin x - Real.cos x) /
    (2 * Real.sin (half x) ^ 2)

theorem gap1 (x : ℝ) (hsin : Real.sin (half x) ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hhalf : HasDerivAt half (1 / 2 : ℝ) x := by
    simpa [half] using (hasDerivAt_id x).div_const (2 : ℝ)
  have hcos :
      HasDerivAt (fun z : ℝ => Real.cos (half z))
        (-Real.sin (half x) * (1 / 2 : ℝ)) x :=
    (Real.hasDerivAt_cos (half x)).comp x hhalf
  have hsin' :
      HasDerivAt (fun z : ℝ => Real.sin (half z))
        (Real.cos (half x) * (1 / 2 : ℝ)) x :=
    (Real.hasDerivAt_sin (half x)).comp x hhalf
  have hcot_raw :
      HasDerivAt (fun z : ℝ => cot (half z))
        (((-Real.sin (half x) * (1 / 2 : ℝ)) * Real.sin (half x) -
            Real.cos (half x) * (Real.cos (half x) * (1 / 2 : ℝ))) /
          Real.sin (half x) ^ 2) x := by
    simpa [cot] using hcos.div hsin' hsin
  have hcot_coeff :
      (((-Real.sin (half x) * (1 / 2 : ℝ)) * Real.sin (half x) -
          Real.cos (half x) * (Real.cos (half x) * (1 / 2 : ℝ))) /
        Real.sin (half x) ^ 2) =
        -(1 / 2 : ℝ) * csc (half x) ^ 2 := by
    unfold csc
    field_simp [hsin] <;>
      nlinarith [Real.sin_sq_add_cos_sq (half x)]
  have hcot :
      HasDerivAt (fun z : ℝ => cot (half z))
        (-(1 / 2 : ℝ) * csc (half x) ^ 2) x := by
    rw [← hcot_coeff]
    exact hcot_raw
  have hy_raw :
      HasDerivAt y
        (Real.exp x * (1 + cot (half x)) +
          Real.exp x * (-(1 / 2 : ℝ) * csc (half x) ^ 2)) x := by
    simpa [y] using
      (Real.hasDerivAt_exp x).mul
        ((hasDerivAt_const x (1 : ℝ)).add hcot)
  have hcoef :
      Real.exp x * (1 + cot (half x)) +
          Real.exp x * (-(1 / 2 : ℝ) * csc (half x) ^ 2) =
        expandedDerivative x := by
    unfold expandedDerivative
    ring
  rw [hcoef] at hy_raw
  exact hy_raw.deriv

theorem gap2 (x : ℝ) (hsin : Real.sin (half x) ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hx : x = half x + half x := by
    unfold half
    ring
  have hsinx :
      Real.sin x =
        Real.sin (half x) * Real.cos (half x) +
          Real.cos (half x) * Real.sin (half x) := by
    calc
      Real.sin x = Real.sin (half x + half x) := congrArg Real.sin hx
      _ = _ := by rw [Real.sin_add]
  have hcosx :
      Real.cos x =
        Real.cos (half x) * Real.cos (half x) -
          Real.sin (half x) * Real.sin (half x) := by
    calc
      Real.cos x = Real.cos (half x + half x) := congrArg Real.cos hx
      _ = _ := by rw [Real.cos_add]
  have hangle :
      2 * Real.sin (half x) ^ 2 +
          2 * Real.sin (half x) * Real.cos (half x) - 1 =
        Real.sin x - Real.cos x := by
    rw [hsinx, hcosx]
    nlinarith [Real.sin_sq_add_cos_sq (half x)]
  unfold expandedDerivative finalDerivative cot csc
  calc
    _ = Real.exp x *
          (2 * Real.sin (half x) ^ 2 +
            2 * Real.sin (half x) * Real.cos (half x) - 1) /
          (2 * Real.sin (half x) ^ 2) := by
      field_simp [hsin]
    _ = _ := by rw [hangle]

theorem gap3 (x : ℝ) (hsin : Real.sin (half x) ≠ 0) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hsin).trans (gap2 x hsin)

end

end ProofGap.Exercise880

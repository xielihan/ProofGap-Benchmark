import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise879

noncomputable section

def bracket (x : ℝ) : ℝ :=
  ((1 - x ^ 2) / 2) * Real.sin x -
    (((1 + x) ^ 2) / 2) * Real.cos x

def y (x : ℝ) : ℝ := bracket x * Real.exp (-x)

def expandedDerivative (x : ℝ) : ℝ :=
  -Real.exp (-x) * bracket x +
    Real.exp (-x) *
      (((1 - x ^ 2) / 2) * Real.cos x - x * Real.sin x +
        (((1 + x) ^ 2) / 2) * Real.sin x -
          (1 + x) * Real.cos x)

def finalDerivative (x : ℝ) : ℝ :=
  x ^ 2 * Real.exp (-x) * Real.sin x

theorem gap1 (x : ℝ) : deriv y x = expandedDerivative x := by
  have hA :
      HasDerivAt (fun t : ℝ => (1 - t ^ 2) / 2) (-x) x := by
    convert
      (((hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).mul (hasDerivAt_id x))).div_const 2)
      using 1
    · funext t
      dsimp
      ring
    · dsimp
      ring
  have hplus : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    convert
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
      using 1 <;> ring
  have hB :
      HasDerivAt (fun t : ℝ => ((1 + t) ^ 2) / 2) (1 + x) x := by
    convert (hplus.mul hplus).div_const 2 using 1
    · funext t
      dsimp
      ring
    · dsimp
      ring
  have hbracket :
      HasDerivAt bracket
        (((1 - x ^ 2) / 2) * Real.cos x - x * Real.sin x +
          (((1 + x) ^ 2) / 2) * Real.sin x -
            (1 + x) * Real.cos x) x := by
    unfold bracket
    convert
      ((hA.mul (Real.hasDerivAt_sin x)).sub
        (hB.mul (Real.hasDerivAt_cos x)))
      using 1 <;> ring
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    convert (hasDerivAt_id x).neg using 1 <;> ring
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x hneg using 1 <;> ring
  unfold y expandedDerivative
  convert (hbracket.mul hexp).deriv using 1 <;> ring
theorem gap2 (x : ℝ) : deriv y x = finalDerivative x := by
  rw [gap1 x]
  unfold expandedDerivative finalDerivative bracket
  ring

end

end ProofGap.Exercise879

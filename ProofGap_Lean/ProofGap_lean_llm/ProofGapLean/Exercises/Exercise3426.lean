import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace ProofGap.Exercise3426

noncomputable section

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

theorem gap1 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hImplicit :
      ∀ x y,
        x * Real.cos (α x y) + y * Real.sin (α x y) +
            Real.log (z x y) =
          f (α x y))
    (hStationary :
      ∀ x y,
        -x * Real.sin (α x y) + y * Real.cos (α x y) =
          deriv f (α x y))
    (hzNonzero : ∀ x y, z x y ≠ 0)
    (hf : Differentiable ℝ f)
    (hα : Differentiable ℝ (Function.uncurry α))
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y,
      Real.cos (α x y) -
          x * Real.sin (α x y) * partialX α x y +
          y * Real.cos (α x y) * partialX α x y +
          partialX z x y / z x y =
        deriv f (α x y) * partialX α x y := by
  intro x y
  have hline :
      DifferentiableAt ℝ (fun s : ℝ => (s, y)) x := by
    refine ⟨
      (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)).prod
        (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)), ?_⟩
    exact (hasDerivAt_id x).prodMk
      (hasDerivAt_const x y)
  have hαx : DifferentiableAt ℝ (fun s : ℝ => α s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (hα (x, y)).comp x hline
  have hzx : DifferentiableAt ℝ (fun s : ℝ => z s y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz (x, y)).comp x hline
  have hcos :
      HasDerivAt (fun s : ℝ => Real.cos (α s y))
        (-Real.sin (α x y) * partialX α x y) x := by
    convert
      (Real.hasDerivAt_cos (α x y)).comp x hαx.hasDerivAt
      using 1 <;>
      simp [Function.comp_def, partialX] <;>
      ring
  have hsin :
      HasDerivAt (fun s : ℝ => Real.sin (α s y))
        (Real.cos (α x y) * partialX α x y) x := by
    convert
      (Real.hasDerivAt_sin (α x y)).comp x hαx.hasDerivAt
      using 1 <;>
      simp [Function.comp_def, partialX] <;>
      ring
  have hlog :
      HasDerivAt (fun s : ℝ => Real.log (z s y))
        (partialX z x y / z x y) x := by
    convert
      (Real.hasDerivAt_log (hzNonzero x y)).comp x hzx.hasDerivAt
      using 1 <;>
      simp [partialX, div_eq_mul_inv] <;>
      ring
  have hleft :
      HasDerivAt
        (fun s : ℝ =>
          s * Real.cos (α s y) + y * Real.sin (α s y) +
            Real.log (z s y))
        (Real.cos (α x y) -
            x * Real.sin (α x y) * partialX α x y +
            y * Real.cos (α x y) * partialX α x y +
            partialX z x y / z x y)
        x := by
    convert
      (((hasDerivAt_id x).mul hcos).add
          ((hasDerivAt_const x y).mul hsin)).add hlog
      using 1 <;>
      simp [partialX] <;>
      ring
  have hright :
      HasDerivAt (fun s : ℝ => f (α s y))
        (deriv f (α x y) * partialX α x y) x := by
    convert
      ((hf (α x y)).hasDerivAt).comp x hαx.hasDerivAt
      using 1 <;>
      simp [Function.comp_def, partialX] <;>
      ring
  have hfun :
      (fun s : ℝ =>
          s * Real.cos (α s y) + y * Real.sin (α s y) +
            Real.log (z s y)) =
        (fun s : ℝ => f (α s y)) := by
    funext s
    exact hImplicit s y
  exact (hleft.deriv.symm).trans
    ((congrArg (fun g : ℝ → ℝ => deriv g x) hfun).trans hright.deriv)

theorem gap2 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hStationary :
      ∀ x y,
        -x * Real.sin (α x y) + y * Real.cos (α x y) =
          deriv f (α x y))
    (hDifferentiated :
      ∀ x y,
        Real.cos (α x y) -
            x * Real.sin (α x y) * partialX α x y +
            y * Real.cos (α x y) * partialX α x y +
            partialX z x y / z x y =
          deriv f (α x y) * partialX α x y) :
    ∀ x y,
      Real.cos (α x y) + partialX z x y / z x y = 0 := by
  intro x y
  have h := hDifferentiated x y
  rw [← hStationary x y] at h
  calc
    Real.cos (α x y) + partialX z x y / z x y =
        (Real.cos (α x y) -
              x * Real.sin (α x y) * partialX α x y +
              y * Real.cos (α x y) * partialX α x y +
              partialX z x y / z x y) -
          ((-x * Real.sin (α x y) + y * Real.cos (α x y)) *
            partialX α x y) := by ring
    _ = 0 := by rw [h]; ring

theorem gap3 (α z : ℝ → ℝ → ℝ)
    (hReduced :
      ∀ x y, Real.cos (α x y) + partialX z x y / z x y = 0)
    (hzNonzero : ∀ x y, z x y ≠ 0) :
    ∀ x y, partialX z x y = -z x y * Real.cos (α x y) := by
  intro x y
  have hdiv :
      partialX z x y / z x y = -Real.cos (α x y) := by
    calc
      partialX z x y / z x y =
          (Real.cos (α x y) + partialX z x y / z x y) -
            Real.cos (α x y) := by ring
      _ = 0 - Real.cos (α x y) := by rw [hReduced x y]
      _ = -Real.cos (α x y) := by ring
  have hmul :
      partialX z x y = (-Real.cos (α x y)) * z x y :=
    (div_eq_iff (hzNonzero x y)).mp hdiv
  calc
    partialX z x y = (-Real.cos (α x y)) * z x y := hmul
    _ = -z x y * Real.cos (α x y) := by ring

theorem gap4 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hImplicit :
      ∀ x y,
        x * Real.cos (α x y) + y * Real.sin (α x y) +
            Real.log (z x y) =
          f (α x y))
    (hStationary :
      ∀ x y,
        -x * Real.sin (α x y) + y * Real.cos (α x y) =
          deriv f (α x y))
    (hzNonzero : ∀ x y, z x y ≠ 0)
    (hf : Differentiable ℝ f)
    (hα : Differentiable ℝ (Function.uncurry α))
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y, partialY z x y = -z x y * Real.sin (α x y) := by
  intro x y
  have hline :
      DifferentiableAt ℝ (fun s : ℝ => (x, s)) y := by
    refine ⟨
      (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)).prod
        (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)), ?_⟩
    exact (hasDerivAt_const y x).prodMk
      (hasDerivAt_id y)
  have hαy : DifferentiableAt ℝ (fun s : ℝ => α x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (hα (x, y)).comp y hline
  have hzy : DifferentiableAt ℝ (fun s : ℝ => z x s) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz (x, y)).comp y hline
  have hcos :
      HasDerivAt (fun s : ℝ => Real.cos (α x s))
        (-Real.sin (α x y) * partialY α x y) y := by
    convert
      (Real.hasDerivAt_cos (α x y)).comp y hαy.hasDerivAt
      using 1 <;>
      simp [Function.comp_def, partialY] <;>
      ring
  have hsin :
      HasDerivAt (fun s : ℝ => Real.sin (α x s))
        (Real.cos (α x y) * partialY α x y) y := by
    convert
      (Real.hasDerivAt_sin (α x y)).comp y hαy.hasDerivAt
      using 1 <;>
      simp [Function.comp_def, partialY] <;>
      ring
  have hlog :
      HasDerivAt (fun s : ℝ => Real.log (z x s))
        (partialY z x y / z x y) y := by
    convert
      (Real.hasDerivAt_log (hzNonzero x y)).comp y hzy.hasDerivAt
      using 1 <;>
      simp [partialY, div_eq_mul_inv] <;>
      ring
  have hleft :
      HasDerivAt
        (fun s : ℝ =>
          x * Real.cos (α x s) + s * Real.sin (α x s) +
            Real.log (z x s))
        (-x * Real.sin (α x y) * partialY α x y +
            Real.sin (α x y) +
            y * Real.cos (α x y) * partialY α x y +
            partialY z x y / z x y)
        y := by
    convert
      (((hasDerivAt_const y x).mul hcos).add
          ((hasDerivAt_id y).mul hsin)).add hlog
      using 1 <;>
      simp [partialY] <;>
      ring
  have hright :
      HasDerivAt (fun s : ℝ => f (α x s))
        (deriv f (α x y) * partialY α x y) y := by
    convert
      ((hf (α x y)).hasDerivAt).comp y hαy.hasDerivAt
      using 1 <;>
      simp [Function.comp_def, partialY] <;>
      ring
  have hfun :
      (fun s : ℝ =>
          x * Real.cos (α x s) + s * Real.sin (α x s) +
            Real.log (z x s)) =
        (fun s : ℝ => f (α x s)) := by
    funext s
    exact hImplicit x s
  have hd :
      -x * Real.sin (α x y) * partialY α x y +
            Real.sin (α x y) +
            y * Real.cos (α x y) * partialY α x y +
            partialY z x y / z x y =
        deriv f (α x y) * partialY α x y := by
    exact (hleft.deriv.symm).trans
      ((congrArg (fun g : ℝ → ℝ => deriv g y) hfun).trans hright.deriv)
  rw [← hStationary x y] at hd
  have hReduced :
      Real.sin (α x y) + partialY z x y / z x y = 0 := by
    calc
      Real.sin (α x y) + partialY z x y / z x y =
          (-x * Real.sin (α x y) * partialY α x y +
                Real.sin (α x y) +
                y * Real.cos (α x y) * partialY α x y +
                partialY z x y / z x y) -
            ((-x * Real.sin (α x y) + y * Real.cos (α x y)) *
              partialY α x y) := by ring
      _ = 0 := by rw [hd]; ring
  have hdiv :
      partialY z x y / z x y = -Real.sin (α x y) := by
    calc
      partialY z x y / z x y =
          (Real.sin (α x y) + partialY z x y / z x y) -
            Real.sin (α x y) := by ring
      _ = 0 - Real.sin (α x y) := by rw [hReduced]
      _ = -Real.sin (α x y) := by ring
  have hmul :
      partialY z x y = (-Real.sin (α x y)) * z x y :=
    (div_eq_iff (hzNonzero x y)).mp hdiv
  calc
    partialY z x y = (-Real.sin (α x y)) * z x y := hmul
    _ = -z x y * Real.sin (α x y) := by ring

theorem gap5 (α z : ℝ → ℝ → ℝ)
    (hX : ∀ x y, partialX z x y = -z x y * Real.cos (α x y)) :
    ∀ x y,
      (partialX z x y) ^ 2 =
        (z x y) ^ 2 * (Real.cos (α x y)) ^ 2 := by
  intro x y
  rw [hX x y]
  ring

theorem gap6 (α z : ℝ → ℝ → ℝ)
    (hY : ∀ x y, partialY z x y = -z x y * Real.sin (α x y)) :
    ∀ x y,
      (partialY z x y) ^ 2 =
        (z x y) ^ 2 * (Real.sin (α x y)) ^ 2 := by
  intro x y
  rw [hY x y]
  ring

theorem gap7 (α z : ℝ → ℝ → ℝ)
    (hX :
      ∀ x y,
        (partialX z x y) ^ 2 =
          (z x y) ^ 2 * (Real.cos (α x y)) ^ 2)
    (hY :
      ∀ x y,
        (partialY z x y) ^ 2 =
          (z x y) ^ 2 * (Real.sin (α x y)) ^ 2) :
    ∀ x y,
      (partialX z x y) ^ 2 + (partialY z x y) ^ 2 =
        (z x y) ^ 2 := by
  intro x y
  rw [hX x y, hY x y]
  calc
    (z x y) ^ 2 * (Real.cos (α x y)) ^ 2 +
          (z x y) ^ 2 * (Real.sin (α x y)) ^ 2 =
        (z x y) ^ 2 *
          ((Real.sin (α x y)) ^ 2 + (Real.cos (α x y)) ^ 2) := by
            ring
    _ = (z x y) ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem gap8 (z : ℝ → ℝ → ℝ)
    (hResult :
      ∀ x y,
        (partialX z x y) ^ 2 + (partialY z x y) ^ 2 =
          (z x y) ^ 2) :
    ∀ x y,
      (partialX z x y) ^ 2 + (partialY z x y) ^ 2 =
        (z x y) ^ 2 := by
  exact hResult

end

end ProofGap.Exercise3426

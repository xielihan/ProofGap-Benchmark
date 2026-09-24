import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3401

noncomputable section

private theorem deriv_eq_zero_of_eventually_const
    (f : ℝ → ℝ) (t d c : ℝ)
    (hf : HasDerivAt f d t)
    (hConst : ∀ᶠ s in nhds t, f s = c) :
    d = 0 := by
  have hEq : f =ᶠ[nhds t] (fun _ : ℝ => c) := hConst
  have hConstDeriv : HasDerivAt (fun _ : ℝ => c) d t :=
    hf.congr_of_eventuallyEq hEq.symm
  exact hConstDeriv.unique (hasDerivAt_const t c)

theorem gap1 (x y : ℝ → ℝ) (t : ℝ)
    (hxDiff : DifferentiableAt ℝ x t)
    (hyDiff : DifferentiableAt ℝ y t)
    (hLinear :
      ∀ᶠ s in nhds t, x s + y s + s = 0) :
    deriv x t + deriv y t + 1 = 0 := by
  have hDeriv :
      HasDerivAt (fun s => x s + y s + s)
        (deriv x t + deriv y t + 1) t := by
    simpa using
      ((hxDiff.hasDerivAt.add hyDiff.hasDerivAt).add (hasDerivAt_id t))
  exact deriv_eq_zero_of_eventually_const _ _ _ _ hDeriv hLinear

theorem gap2 (x y : ℝ → ℝ) (t : ℝ)
    (hxDiff : DifferentiableAt ℝ x t)
    (hyDiff : DifferentiableAt ℝ y t)
    (hSphere :
      ∀ᶠ s in nhds t, (x s) ^ 2 + (y s) ^ 2 + s ^ 2 = 1) :
    x t * deriv x t + y t * deriv y t + t = 0 := by
  have hxSq :
      HasDerivAt (fun s => (x s) ^ 2) (2 * x t * deriv x t) t := by
    convert hxDiff.hasDerivAt.mul hxDiff.hasDerivAt using 1 <;>
      (try funext s) <;>
      (try simp [pow_two]) <;>
      ring
  have hySq :
      HasDerivAt (fun s => (y s) ^ 2) (2 * y t * deriv y t) t := by
    convert hyDiff.hasDerivAt.mul hyDiff.hasDerivAt using 1 <;>
      (try funext s) <;>
      (try simp [pow_two]) <;>
      ring
  have htSq :
      HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).mul (hasDerivAt_id t) using 1 <;>
      (try funext s) <;>
      (try simp [pow_two]) <;>
      ring
  have hDeriv :
      HasDerivAt (fun s => (x s) ^ 2 + (y s) ^ 2 + s ^ 2)
        (2 * x t * deriv x t + 2 * y t * deriv y t + 2 * t) t :=
    (hxSq.add hySq).add htSq
  have hZero :=
    deriv_eq_zero_of_eventually_const _ _ _ _ hDeriv hSphere
  linarith

theorem gap3 (x y : ℝ → ℝ) (t : ℝ)
    (hNonzero : x t - y t ≠ 0)
    (hLinearDerivative : deriv x t + deriv y t + 1 = 0)
    (hSphereDerivative :
      x t * deriv x t + y t * deriv y t + t = 0) :
    deriv x t = (y t - t) / (x t - y t) := by
  field_simp [hNonzero]
  linear_combination hSphereDerivative - y t * hLinearDerivative

theorem gap4 (x y : ℝ → ℝ) (t : ℝ)
    (hNonzero : x t - y t ≠ 0)
    (hLinearDerivative : deriv x t + deriv y t + 1 = 0)
    (hSphereDerivative :
      x t * deriv x t + y t * deriv y t + t = 0)
    (hxFormula : deriv x t = (y t - t) / (x t - y t)) :
    deriv y t = (t - x t) / (x t - y t) := by
  field_simp [hNonzero]
  linear_combination x t * hLinearDerivative - hSphereDerivative

end

end ProofGap.Exercise3401

import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ProofGap.Exercise3302

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (a b c : ℝ)
    (hu : ∀ x y z, u x y z = f (a * x + b * y + c * z))
    (n : ℕ) (hf : ContDiff ℝ n f)
    (x y z dx dy dz : ℝ) :
    nthDifferential n u x y z dx dy dz =
      iterDeriv n f (a * x + b * y + c * z) *
        (a * dx + b * dy + c * dz) ^ n := by
  let A : ℝ := a * x + b * y + c * z
  let D : ℝ := a * dx + b * dy + c * dz
  have hline :
      (fun s : ℝ => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        fun s : ℝ => f (A + D * s) := by
    funext s
    rw [hu]
    dsimp [A, D]
    congr 1
    ring
  have hg : ContDiff ℝ n (fun t : ℝ => f (A + t)) := by
    fun_prop
  have hscale :=
    congrFun
      (iteratedDeriv_comp_const_mul
        (f := fun t : ℝ => f (A + t)) hg D) 0
  rw [iteratedDeriv_comp_const_add] at hscale
  simp only [mul_zero, add_zero] at hscale
  rw [nthDifferential, hline]
  simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
  simpa [A, D, mul_comm] using hscale

end

end ProofGap.Exercise3302

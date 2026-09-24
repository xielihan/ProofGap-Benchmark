import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1262

noncomputable section

def weighted (y : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  y x * Real.exp (-lam * x)

private theorem eq_of_deriv_eq_zero {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hzero : ∀ x, deriv f x = 0)
    (x y : ℝ) : f x = f y := by
  exact is_const_of_deriv_eq_zero hf hzero x y

theorem gap1 (y : ℝ → ℝ) (lam x : ℝ) (hy : DifferentiableAt ℝ y x) :
    deriv (weighted y lam) x =
      deriv y x * Real.exp (-lam * x) -
        lam * y x * Real.exp (-lam * x) := by
  have hlin : HasDerivAt (fun z : ℝ => (-lam) * z) (-lam) x := by
    simpa using (hasDerivAt_id x).const_mul (-lam)
  have hexp :
      HasDerivAt (fun z : ℝ => Real.exp (-lam * z))
        (Real.exp (-lam * x) * (-lam)) x :=
    (Real.hasDerivAt_exp (-lam * x)).comp x hlin
  calc
    deriv (weighted y lam) x =
        deriv y x * Real.exp (-lam * x) +
          y x * (Real.exp (-lam * x) * (-lam)) :=
      (hy.hasDerivAt.mul hexp).deriv
    _ = deriv y x * Real.exp (-lam * x) -
          lam * y x * Real.exp (-lam * x) := by ring

theorem gap2 (y : ℝ → ℝ) (lam x : ℝ) (hode : deriv y x = lam * y x) :
    deriv y x * Real.exp (-lam * x) -
        lam * y x * Real.exp (-lam * x) =
      lam * y x * Real.exp (-lam * x) -
        lam * y x * Real.exp (-lam * x) := by
  rw [hode]

theorem gap3 (y : ℝ → ℝ) (lam x : ℝ) :
    lam * y x * Real.exp (-lam * x) -
      lam * y x * Real.exp (-lam * x) = 0 := by
  ring

theorem gap4 (y : ℝ → ℝ) (lam : ℝ) (hy : Differentiable ℝ y)
    (hode : ∀ x, deriv y x = lam * y x) :
    ∀ x, deriv (weighted y lam) x = 0 := by
  intro x
  rw [gap1 y lam x (hy x), hode x]
  ring

theorem gap5 (y : ℝ → ℝ) (lam : ℝ) (hy : Differentiable ℝ y)
    (hode : ∀ x, deriv y x = lam * y x) :
    ∃ C, ∀ x, weighted y lam x = C := by
  have hlin : Differentiable ℝ (fun x : ℝ => -lam * x) :=
    (differentiable_const (-lam)).mul differentiable_id
  have hw : Differentiable ℝ (weighted y lam) := by
    unfold weighted
    exact hy.mul (Real.differentiable_exp.comp hlin)
  refine ⟨weighted y lam 0, ?_⟩
  intro x
  exact eq_of_deriv_eq_zero hw (gap4 y lam hy hode) x 0

theorem gap6 (y : ℝ → ℝ) (lam : ℝ) (hy : Differentiable ℝ y)
    (hode : ∀ x, deriv y x = lam * y x) :
    ∃ C, ∀ x, y x = C * Real.exp (lam * x) := by
  obtain ⟨C, hC⟩ := gap5 y lam hy hode
  refine ⟨C, ?_⟩
  intro x
  have hCx : y x * Real.exp (-lam * x) = C := by
    simpa only [weighted] using hC x
  have hexp :
      Real.exp (-lam * x) * Real.exp (lam * x) = 1 := by
    calc
      Real.exp (-lam * x) * Real.exp (lam * x) =
          Real.exp ((-lam * x) + lam * x) :=
        (Real.exp_add (-lam * x) (lam * x)).symm
      _ = Real.exp 0 := by congr 1 <;> ring
      _ = 1 := Real.exp_zero
  calc
    y x = y x * 1 := by simp
    _ = y x * (Real.exp (-lam * x) * Real.exp (lam * x)) := by
      rw [hexp]
    _ = (y x * Real.exp (-lam * x)) * Real.exp (lam * x) := by ring
    _ = C * Real.exp (lam * x) := by rw [hCx]

theorem gap7 (y : ℝ → ℝ) (lam : ℝ) (hy : Differentiable ℝ y)
    (hode : ∀ x, deriv y x = lam * y x) :
    ∃ C, ∀ x, y x = C * Real.exp (lam * x) := by
  exact gap6 y lam hy hode

end

end ProofGap.Exercise1262
